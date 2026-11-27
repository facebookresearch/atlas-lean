# JOB SHOP WITH A FIXED NUMBER OF JOBS, WEIGHTED TARDINESS is NP-complete

For every natural number $k \ge 3$, the decision problem JOB SHOP WITH A FIXED NUMBER OF JOBS, WEIGHTED TARDINESS belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N (`J3|n=3|C_max` is NP-hard).
- M. Middendorf and V. G. Timkovsky, "Transversal graphs for partially ordered sets: sequencing, merging and scheduling problems", Journal of Combinatorial Optimization 3 (1999), 417-435, doi:10.1023/A:1009827520712 (pseudo-polynomial algorithm for each fixed `k`).
- P. Brucker and S. Knust, *Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop` (job shop problems without preemption): `J|prec;r_i;n=k|Σw_iT_i` maximal pseudo-polynomially solvable (Middendorf and Timkovsky 1999), `J3|n=3|C_max` minimal NP-hard (Sotskov and Shakhlevich 1995).
