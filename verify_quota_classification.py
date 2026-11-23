#!/usr/bin/env python3
"""
Computational checks for the section "Quota Compliance and an Impossibility Theorem" of

    T. C. Wunder and J. W. Cutrone,
    "The Classification of Electoral College Flips and an Impossibility Theorem".

Usage
-----
Python 3.8 or later is required; only the standard library is used.

    python3 verify_quota_classification.py                quick run of every check (a few seconds)
    python3 verify_quota_classification.py --six-states   the six-state verification reported in
                                                          Appendix A (about three minutes)
    python3 verify_quota_classification.py --full         every check on the grids reported in the
                                                          paper (about three minutes)
    python3 verify_quota_classification.py --1876         the 1876 computation of Appendix B only

Each run ends with the line "ALL CHECKS PASSED" or "SOME CHECKS FAILED"; the exit status is 0 or 1.

To reproduce the six-state verification of Appendix A, run the script with --six-states.  It
enumerates every quota vector for six states whose entries are multiples of 1/k, for
(M, k) = (6, 24), (12, 12), (18, 8), (24, 6), (30, 5), (36, 4), (48, 3), one representative for each
vector up to reordering of the states (6,013,625 quota vectors in all).  For each of them it computes
the surplus set selected in the proof of the six-state theorem and checks, by enumerating all
coalitions, that the resulting apportionment admits no electoral flip.  The expected output is

    Avoidable flips, six states, 6 | M: 6013625 quota vectors ...; failures: 0
    ALL CHECKS PASSED

What is checked
---------------
1. Unavoidable flips.  For every pair (n, M) with 4 <= n <= 12 and n <= M <= 48 for which the paper
   proves that every apportionment method satisfying quota admits an electoral flip, the quota vector
   used in the proof is rebuilt exactly as written, every apportionment satisfying quota for that
   vector is enumerated, and each one is confirmed to admit an electoral flip.

2. Avoidable flips.  For every quota vector whose entries are multiples of 1/k (one representative of
   each vector up to reordering the states), the surplus set selected in the proofs is computed and
   confirmed to admit no electoral flip, by brute force over all coalitions.  This is done for
       three states and odd M,
       four states and even M   (largest fractional parts, i.e. Hamilton's method),
       five states and even M,
       six states and 6 | M     (the case analysis proved in Appendix A).

3. The election of 1876.  The state-level table of Appendix B is recomputed from the 1870 census
   populations, the House seats in force in 1876, and the officially recognized electoral votes;
   quota compliance and the electoral flip are confirmed.

Notation follows the paper: b_i = lower quotas, d_i = fractional parts, D = number of surplus seats,
F = set of fractional states, W = surplus set.  All arithmetic is exact: a quota vector is stored as
integer numerators K_i over a common denominator `den`, so q_i = K_i / den.
"""
import itertools
import math
import sys
import time
from fractions import Fraction as Fr
from itertools import combinations


# --------------------------------------------------------------------------------------------------
# Basic tools
# --------------------------------------------------------------------------------------------------
def partitions(total, parts, maxpart=None):
    """Nonincreasing positive integer partitions of `total` into exactly `parts` parts."""
    if maxpart is None:
        maxpart = total
    if parts == 1:
        if 1 <= total <= maxpart:
            yield (total,)
        return
    lo = -(-total // parts)
    hi = min(maxpart, total - (parts - 1))
    for k in range(hi, lo - 1, -1):
        for rest in partitions(total - k, parts - 1, k):
            yield (k,) + rest


def has_flip(K, den, M, W):
    """True if the apportionment a_i = floor(q_i) + [i in W] admits an electoral flip.

    A coalition S flips when its candidate wins the proportional Electoral College and loses the
    actual one.  The opposite case is the same condition for the complementary coalition, so
    checking every coalition covers both.
    """
    n = len(K)
    total = M + 2 * n                      # all electoral votes
    w = [K[i] + 2 * den for i in range(n)]                  # proportional votes, times den
    v = [K[i] // den + 2 + (1 if i in W else 0) for i in range(n)]   # actual votes
    size = 1 << n
    ws = [0] * size
    vs = [0] * size
    for mask in range(1, size):
        low = (mask & -mask).bit_length() - 1
        prev = mask & (mask - 1)
        ws[mask] = ws[prev] + w[low]
        vs[mask] = vs[prev] + v[low]
        if 2 * ws[mask] > total * den and 2 * vs[mask] < total:
            return True
    return False


def surplus_data(K, den, M):
    b = [k // den for k in K]
    d = [k % den for k in K]               # fractional parts, times den
    D = M - sum(b)
    F = [i for i in range(len(K)) if d[i] > 0]
    return b, d, D, F


def to_int(q):
    den = 1
    for x in q:
        den = den * x.denominator // math.gcd(den, x.denominator)
    return [int(x * den) for x in q], den


# --------------------------------------------------------------------------------------------------
# 1. Unavoidable flips: the quota vectors used in the proofs
# --------------------------------------------------------------------------------------------------
EPS = Fr(1, 200)        # the proofs need 0 < eps < 1/15
ETA = Fr(1, 12)         # the five-state proof needs 0 < eta < 1/6


def four_states_odd(M):
    m = Fr(M, 4)
    if M % 4 == 1:
        return [m + EPS] * 3 + [m - 3 * EPS]
    return [m - EPS] * 3 + [m + 3 * EPS]


def five_states_odd(M):
    return [Fr(M + 1, 2) + ETA, Fr(M - 3, 2) - ETA, Fr(1, 3), Fr(1, 3), Fr(1, 3)]


def six_states_even(M):
    assert M % 2 == 0 and M % 6 != 0
    rho = M % 6
    sigma = 1 if rho == 2 else -1
    m = Fr(M, 6)
    return [m + sigma * EPS] * 5 + [m - 5 * sigma * EPS]


def seven_states_even(M):
    assert M % 2 == 0 and M >= 8
    c = 1 if (M - 4) % 6 != 0 else 2
    rho = (M - 2 - 2 * c) % 6
    assert rho in (2, 4)
    sigma = 1 if rho == 2 else -1
    m = Fr(M - 2 - 2 * c, 6)
    return [m + sigma * EPS] * 5 + [c + 2 + m - 5 * sigma * EPS, Fr(c)]


def unavoidable(n, M):
    """The range in which the paper proves that every quota method admits a flip."""
    return n >= 7 or (n == 6 and M % 6 != 0) or (n in (4, 5) and M % 2 == 1)


def forcing_vector(n, M):
    """The quota vector used in the proof for n states and M seats (extension by pairs included)."""
    if M % 2 == 1:
        n0 = 4 if n % 2 == 0 else 5
        t = (n - n0) // 2
        M0 = M - 2 * t
        base = four_states_odd(M0) if n0 == 4 else five_states_odd(M0)
        return base + [Fr(1)] * (2 * t)
    if n == 6:
        return six_states_even(M)
    if n == 7:
        return seven_states_even(M)
    if n % 2 == 0:
        t = (n - 6) // 2
        K = t if (M - 2 * t) % 6 != 0 else t + 1
        ks = [1] * (t - 1) + [K - (t - 1)]
        q = six_states_even(M - 2 * K)
    else:
        t = (n - 7) // 2
        ks = [1] * t
        q = seven_states_even(M - 2 * t)
    for k in ks:
        q = q + [Fr(k), Fr(k)]
    return q


def check_unavoidable(n_max, m_max):
    pairs = failures = 0
    for n in range(4, n_max + 1):
        for M in range(n, m_max + 1):
            if not unavoidable(n, M):
                continue
            q = forcing_vector(n, M)
            assert len(q) == n and sum(q) == M and min(q) > 0
            K, den = to_int(q)
            b, d, D, F = surplus_data(K, den, M)
            pairs += 1
            if not all(has_flip(K, den, M, set(W)) for W in combinations(F, D)):
                failures += 1
                print("   FAILURE: some quota apportionment has no flip for", (n, M))
    return pairs, failures


# --------------------------------------------------------------------------------------------------
# 2. Avoidable flips: the surplus sets selected in the proofs
# --------------------------------------------------------------------------------------------------
def rule_three_states_odd(K, den, M):
    """All surplus sets allowed by the proof for three states and odd M."""
    b, d, D, F = surplus_data(K, den, M)
    special = [i for i in range(3) if (M + 1) * den < 2 * K[i] < (M + 3) * den]
    allowed = []
    for W in combinations(F, D):
        if special:
            i = special[0]
            if 2 * K[i] > (M + 2) * den and i not in W:      # q_i > T: state i must get a surplus seat
                continue
            if 2 * K[i] < (M + 2) * den and i in W:          # q_i < T: state i must not
                continue
        allowed.append(set(W))
    return allowed


def rule_four_states_even(K, den, M):
    b, d, D, F = surplus_data(K, den, M)
    return set(sorted(F, key=lambda i: -d[i])[:D])


def rule_five_states_even(K, den, M):
    n = 5
    b, d, D, F = surplus_data(K, den, M)
    if D <= 1:
        return set(F[:D])
    critical = [P for P in combinations(range(n), 2) if b[P[0]] + b[P[1]] == M // 2]
    if not critical:
        return set(F[:D])
    common = set(range(n))
    for P in critical:
        common &= set(P)
    if common:                                               # common state x
        x = min(common)
        if d[x] == 0:
            return set(F[:D])
        Fp = [i for i in F if i != x]
        leaves = [j for P in critical for j in P if j != x]
        Y_gt = [y for y in leaves if d[x] + d[y] > den]
        Y_lt = [y for y in leaves if d[y] > 0 and d[x] + d[y] < den]
        if len(Y_gt) <= D:
            W = set(Y_gt)
            W |= set([i for i in Fp if i not in W][:D - len(W)])
            return W
        return {x} | set([i for i in Fp if i not in Y_lt][:D - 1])
    x, y, z = sorted(set(i for P in critical for i in P), key=lambda i: -d[i])   # triangle
    J = [i for i in range(n) if i not in (x, y, z) and d[i] > 0]
    t = len(J)
    if d[x] + d[y] >= den:
        return {x, y} | set(J[:D - 2])
    if D <= t:
        return set(J[:D])
    return set(J) | {x}


def choose_pair(b, phi, den, mu, rho):
    """The pair R of the lemma 'Choosing a pair' (phi is given as numerators over den, sum = 2 den)."""
    n = 6
    balanced_value = 3 * mu - rho // 2
    F = [i for i in range(n) if phi[i] > 0]
    B = lambda S: sum(b[i] for i in S)
    Phi = lambda S: sum(phi[i] for i in S)
    critical = [P for P in combinations(range(n), 2) if B(P) == 3 * mu + 1]
    for P in critical:                                       # Step 1
        if Phi(P) >= den:
            return set(P)
    if not critical:                                         # Step 2
        if len(F) == 3:
            return set(F[:2])
        if len(F) == 4:
            return set(sorted(F, key=lambda i: -phi[i])[:2])
        if len(F) == 5:
            s = sorted(F, key=lambda i: -phi[i])
            rest = tuple(s[2:])
            if B(rest) == balanced_value and Phi(rest) > den:
                S0 = next(S for S in combinations(F, 3) if B(S) != balanced_value)
                return set(F) - set(S0)
            return set(s[:2])
        s = sorted(range(n), key=lambda i: -b[i])
        top, bottom = (s[0], s[1]), (s[4], s[5])
        in_balanced = lambda P: any(B(P + (i,)) == balanced_value for i in range(n) if i not in P)
        if not in_balanced(top):
            return set(top)
        assert not in_balanced(bottom)
        return set(bottom)
    x, y = critical[0]                                       # Step 3
    if phi[x] < phi[y]:
        x, y = y, x
    z1, z2, z3, z4 = sorted([i for i in range(n) if i not in (x, y)], key=lambda i: -phi[i])
    if B((x, z3, z4)) == balanced_value and Phi((x, z3, z4)) > den:
        return {x, z3}
    return {z1, z2}


def rule_six_states(K, den, M):
    """The safe surplus set selected in the proof for six states and 6 | M."""
    n = 6
    assert M % 6 == 0
    mu = M // 6
    b, d, D, F = surplus_data(K, den, M)
    B = lambda S: sum(b[i] for i in S)
    Dsum = lambda S: sum(d[i] for i in S)
    critical = [P for P in combinations(range(n), 2) if B(P) == 3 * mu + 1]

    def common_state(pairs, pool):
        common = set(pool)
        for P in pairs:
            common &= set(P)
        assert common
        return min(common)

    if D <= 1:
        return set(F[:D])
    if D == 2:
        return choose_pair(b, d, den, mu, 2)
    if D == 4:
        if len(F) == 5:
            light = [P for P in critical if Dsum(P) < den and set(P) <= set(F)]
            return set(F) - {common_state(light, F)}
        return set(range(n)) - choose_pair(b, [den - x for x in d], den, mu, 4)
    if D == 5:
        light = [P for P in critical if Dsum(P) < den]
        return set(range(n)) - {common_state(light, range(n))}
    # D == 3
    for L in combinations(range(n), 3):
        if B(L) == 3 * mu - 2 and Dsum(L) > 2 * den:
            return set(L)
    if not critical:
        return set(next(S for S in combinations(F[:4], 3) if B(S) != 3 * mu - 2))
    common = set(range(n))
    for P in critical:
        common &= set(P)
    if not common:                                           # triangle
        x, y, z = sorted(set(i for P in critical for i in P), key=lambda i: -d[i])
        J = [i for i in range(n) if i not in (x, y, z) and d[i] > 0]
        if d[x] + d[y] >= den:
            return {x, y, J[0]}
        if len(J) == 3:
            return set(J)
        return set(J) | {x}
    x = min(common)                                          # common state
    Y = [j for P in critical for j in P if j != x]
    if d[x] == 0:
        if not set(Y) <= set(F):
            return set(F[:3])
        return set([i for i in F if i != Y[0]][:3])
    Fx = [i for i in F if i != x]
    Y_lt = [y for y in Y if d[x] + d[y] < den]
    not_light = [y for y in Y if d[x] + d[y] >= den]
    if not_light:
        y1 = not_light[0]
        others = [u for u in Fx if u != y1 and u not in Y_lt]
        if others:
            return {x, y1, others[0]}
        return {y1} | set([u for u in Fx if u != y1][:2])
    return set(next(W for W in combinations(Fx, 3) if not set(Y) <= set(W)))


def check_rule(n, M, den, rule):
    vectors = failures = 0
    for K in partitions(M * den, n):
        K = list(K)
        b, d, D, F = surplus_data(K, den, M)
        result = rule(K, den, M)
        candidates = result if isinstance(result, list) else [result]
        vectors += 1
        for W in candidates:
            assert len(W) == D and all(d[i] > 0 for i in W), (K, W)
            if has_flip(K, den, M, W):
                failures += 1
                print("   FAILURE: flip for quota numerators", K, "over", den, "with surplus set", sorted(W))
    return vectors, failures


# --------------------------------------------------------------------------------------------------
# 3. The election of 1876 (Appendix B)
# --------------------------------------------------------------------------------------------------
# (state, 1870 census population, House seats in force in 1876, candidate: H = Hayes, T = Tilden)
DATA_1876 = [
    ("Alabama",         996992,  8, "T"), ("Arkansas",        484471,  4, "T"),
    ("California",      560247,  4, "H"), ("Colorado",         39864,  1, "H"),
    ("Connecticut",     537454,  4, "T"), ("Delaware",        125015,  1, "T"),
    ("Florida",         187748,  2, "H"), ("Georgia",        1184109,  9, "T"),
    ("Illinois",       2539891, 19, "H"), ("Indiana",        1680637, 13, "T"),
    ("Iowa",           1194020,  9, "H"), ("Kansas",          364399,  3, "H"),
    ("Kentucky",       1321011, 10, "T"), ("Louisiana",       726915,  6, "H"),
    ("Maine",           626915,  5, "H"), ("Maryland",        780894,  6, "T"),
    ("Massachusetts",  1457351, 11, "H"), ("Michigan",       1184059,  9, "H"),
    ("Minnesota",       439706,  3, "H"), ("Mississippi",     827922,  6, "T"),
    ("Missouri",       1721295, 13, "T"), ("Nebraska",        122993,  1, "H"),
    ("Nevada",           42491,  1, "H"), ("New Hampshire",   318300,  3, "H"),
    ("New Jersey",      906096,  7, "T"), ("New York",       4382759, 33, "T"),
    ("North Carolina", 1071361,  8, "T"), ("Ohio",           2665260, 20, "H"),
    ("Oregon",           90923,  1, "H"), ("Pennsylvania",   3521951, 27, "H"),
    ("Rhode Island",    217353,  2, "H"), ("South Carolina",  705606,  5, "H"),
    ("Tennessee",      1258520, 10, "T"), ("Texas",           818579,  6, "T"),
    ("Vermont",         330551,  3, "H"), ("Virginia",       1225163,  9, "T"),
    ("West Virginia",   442014,  3, "T"), ("Wisconsin",      1054670,  8, "H"),
]


def check_1876(show_table=False):
    M = sum(seats for _, _, seats, _ in DATA_1876)
    P = sum(pop for _, pop, _, _ in DATA_1876)
    quota = {name: Fr(M * pop, P) for name, pop, _, _ in DATA_1876}
    if show_table:
        print(f"{'State':<16}{'Population':>12}{'Seats':>7}{'Quota':>10}{'Seats-Quota':>13}  Candidate")
        for name, pop, seats, cand in DATA_1876:
            print(f"{name:<16}{pop:>12,}{seats:>7}{float(quota[name]):>10.3f}{float(seats - quota[name]):>+13.3f}  "
                  f"{'Hayes' if cand == 'H' else 'Tilden'}")
    within_quota = all(math.floor(quota[name]) <= seats <= math.ceil(quota[name])
                       for name, _, seats, _ in DATA_1876)
    worst = max(abs(seats - quota[name]) for name, _, seats, _ in DATA_1876)
    states = {c: sum(1 for *_, cand in DATA_1876 if cand == c) for c in "HT"}
    seats = {c: sum(a for _, _, a, cand in DATA_1876 if cand == c) for c in "HT"}
    q = {c: sum(quota[name] for name, _, _, cand in DATA_1876 if cand == c) for c in "HT"}
    actual = {c: seats[c] + 2 * states[c] for c in "HT"}
    prop = {c: q[c] + 2 * states[c] for c in "HT"}
    flip = (actual["H"] - actual["T"]) * (prop["H"] - prop["T"]) < 0
    print(f"Election of 1876: n = {len(DATA_1876)}, M = {M}, total population {P:,}; "
          f"actual {actual['H']}-{actual['T']} (Hayes-Tilden), proportional "
          f"{float(prop['H']):.3f}-{float(prop['T']):.3f}; every state within quota: {within_quota} "
          f"(largest |seats - quota| = {float(worst):.3f}); electoral flip: {flip}")
    expected = (len(DATA_1876) == 38 and M == 293 and P == 38155505 and actual == {"H": 185, "T": 184}
                and within_quota and flip)
    return expected


# --------------------------------------------------------------------------------------------------
def main():
    args = set(sys.argv[1:])
    unknown = args - {"--full", "--six-states", "--1876"}
    if unknown:
        print("unknown option(s):", " ".join(sorted(unknown)))
        print(__doc__)
        return 2
    full = "--full" in args
    only_six = "--six-states" in args and not full
    only_1876 = "--1876" in args and not full and not only_six
    start = time.time()
    ok = True

    six_state_grid = [(6, 24), (12, 12), (18, 8), (24, 6), (30, 5), (36, 4), (48, 3)]
    grids = {
        "three states, odd M": (3, rule_three_states_odd,
                                [(3, 24), (5, 24), (7, 24), (9, 12), (11, 12), (13, 12)] if full
                                else [(3, 12), (5, 12), (7, 12)]),
        "four states, even M": (4, rule_four_states_even,
                                [(4, 12), (6, 12), (8, 12), (10, 10), (12, 20), (20, 12), (30, 6)] if full
                                else [(4, 12), (6, 12), (8, 6)]),
        "five states, even M": (5, rule_five_states_even,
                                [(6, 12), (8, 12), (10, 10), (12, 8), (14, 6), (16, 6), (20, 6), (30, 4)] if full
                                else [(6, 8), (8, 6), (10, 4)]),
        "six states, 6 | M": (6, rule_six_states,
                              six_state_grid if (full or only_six) else [(6, 10), (12, 5), (18, 3)]),
    }
    if only_six:
        grids = {"six states, 6 | M": grids["six states, 6 | M"]}

    if not only_six and not only_1876:
        n_max, m_max = (12, 48) if full else (10, 30)
        pairs, failures = check_unavoidable(n_max, m_max)
        ok &= failures == 0
        print(f"Unavoidable flips: {pairs} pairs (n, M) with 4 <= n <= {n_max}, n <= M <= {m_max}; "
              f"failures: {failures}")

    if not only_1876:
        for name, (n, rule, grid) in grids.items():
            total = bad = 0
            for M, den in grid:
                vectors, failures = check_rule(n, M, den, rule)
                total += vectors
                bad += failures
            ok &= bad == 0
            print(f"Avoidable flips, {name}: {total} quota vectors on the grids (M, k) = {grid}; "
                  f"failures: {bad}")

    if not only_six:
        ok &= check_1876(show_table=only_1876)

    print(f"{'ALL CHECKS PASSED' if ok else 'SOME CHECKS FAILED'}  [{time.time() - start:.0f} s]")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
