# Supplementary code: computational verification

This folder accompanies

> T. C. Wunder and J. W. Cutrone, *The Classification of Electoral College Flips and an Impossibility Theorem*.

The single script `verify_quota_classification.py` reproduces the computational checks described in
Remark A.2 (Appendix A) and the state-level computation for the election of 1876 (Appendix B).

## Requirements

Python 3.8 or later. Only the standard library is used; nothing needs to be installed.

## Reproducing the six-state verification (Appendix A)

```
python3 verify_quota_classification.py --six-states
```

The script enumerates every quota vector for six states whose entries are multiples of 1/k, for

(M, k) = (6, 24), (12, 12), (18, 8), (24, 6), (30, 5), (36, 4), (48, 3),

taking one representative of each vector up to reordering of the states (6,013,625 quota vectors in
all). For each quota vector it computes the surplus set selected in the proof of the six-state theorem
and checks, by enumerating all coalitions, that the resulting apportionment admits no electoral flip.

Expected output (the running time is two to three minutes on a current laptop):

```
Avoidable flips, six states, 6 | M: 6013625 quota vectors on the grids (M, k) = [(6, 24), (12, 12), (18, 8), (24, 6), (30, 5), (36, 4), (48, 3)]; failures: 0
ALL CHECKS PASSED  [122 s]
```

## Other options

| Command | What it does | Time |
|---|---|---|
| `python3 verify_quota_classification.py` | Quick run of every check on small grids | a few seconds |
| `python3 verify_quota_classification.py --six-states` | The six-state verification of Appendix A | 2–3 minutes |
| `python3 verify_quota_classification.py --full` | Every check on the grids reported in the paper | about 3 minutes |
| `python3 verify_quota_classification.py --1876` | Prints the state-level table of Appendix B and confirms quota compliance and the electoral flip | instant |

Every run ends with `ALL CHECKS PASSED` or `SOME CHECKS FAILED`, and the exit status is 0 or 1.

## What is checked

1. **Unavoidable flips.** For every pair (n, M) with 4 ≤ n ≤ 12 and n ≤ M ≤ 48 that satisfies the
   hypotheses of the impossibility theorem (316 pairs with `--full`), the quota vector used in the
   proof is rebuilt exactly as written, every apportionment that satisfies quota for it is enumerated,
   and each one is confirmed to admit an electoral flip.
2. **Avoidable flips.** The surplus sets selected in the proofs for three states (odd M), four states
   (even M), five states (even M), and six states (6 | M) are computed for every quota vector on a
   grid and confirmed to admit no electoral flip.
3. **The election of 1876.** The quotas, discrepancies, and electoral totals of Appendix B are
   recomputed from the 1870 census populations, the House seats in force in 1876, and the officially
   recognized electoral votes.

All arithmetic is exact: quotas are stored as integer numerators over a common denominator.
