# NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax is NP-complete

The NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a number `m ≥ 1` of machines `M_1, …, M_m` in an open shop, `n` jobs, each job `j` consisting of `m` operations `O_j1, …, O_jm` with processing times `p_jk = 1`, where `O_jk` is processed on `M_k` and the operations of a job may be processed in any order, but no two of them at the same time; an out-tree precedence relation on the jobs (out-forest: each job has at most one immediate predecessor; if `i` precedes `j`, then no operation of `j` starts before every operation of `i` is completed); an integer due date `d_j` for each job `j`; and an integer bound `K`. Each machine processes at most one operation at a time, and no job waits: there is no waiting time between consecutive operations of a job. Question: is there a schedule whose maximum lateness `max_j (C_j - d_j)` is at most `K`, where `C_j` is the completion time of job `j` (of its last operation)?

## Sources

- P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables (class "Open-shop problems with no-wait", minimal NP-hard entry `O | p_ij = 1; outtree; no-wait | L_max`, NP-hard in the strong sense, credited to Brucker, Garey and Johnson (1977)).
- P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2(3) (1977), 275-284, doi:10.1287/moor.2.3.275.
