# OPEN SHOP O|p_ij=1;outtree;r_i|Cmax is NP-complete

The OPEN SHOP O|p_ij=1;outtree;r_i|Cmax decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a number `m ≥ 1` of machines `M_1, …, M_m` in an open shop, `n` jobs, each job `j` consisting of `m` operations `O_j1, …, O_jm` with processing times `p_jk = 1`, where `O_jk` is processed on `M_k` and the operations of a job may be processed in any order, but no two of them at the same time; an out-tree precedence relation on the jobs (out-forest: each job has at most one immediate predecessor; if `i` precedes `j`, then no operation of `j` starts before every operation of `i` is completed); a release date `r_j ∈ ℕ` for each job `j` (no operation of `j` starts before `r_j`); and a bound `K`. Each machine processes at most one operation at a time. Question: is there a schedule whose makespan `max_j C_j` is at most `K`, where `C_j` is the completion time of job `j` (of its last operation)?

## Sources

- P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables (class "Open-shop problems without preemption", minimal NP-hard entry `O | p_ij = 1; outtree; r_i | C_max`, NP-hard in the strong sense, credited to Timkovsky (2003)).
- V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376, doi:10.1016/S0377-2217(02)00767-1.
