# OPEN SHOP O|p_ij=1;outtree|Lmax is NP-complete

The OPEN SHOP O|p_ij=1;outtree|Lmax decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: $m \ge 1$ machines $M_1, \dots, M_m$ in an open shop; $n \ge 0$ jobs, each consisting of $m$ operations $O_{j1}, \dots, O_{jm}$ of unit length, $O_{jk}$ processed on $M_k$, in any order but no two of them at the same time; each machine processes one operation at a time; an out-tree precedence relation on the jobs (out-forest: each job has at most one immediate predecessor), where $i$ preceding $j$ means that no operation of $j$ starts before every operation of $i$ is completed; an integer due date $d_j$ for each job $j$; and an integer bound $K$. Question: is there a schedule with natural-number start times in which every operation of every job $j$ completes by time $d_j + K$? When $n \ge 1$, this says that the maximum lateness $\max_j (C_j - d_j)$ is at most $K$, where $C_j$ is the completion time of job $j$ (of its last operation); when $n = 0$, every bound $K$, negative ones included, gives a yes-instance.

## Sources

- P. Brucker and S. Knust, *Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/, class o_nop (open shop problems without preemption), entry $O \mid p_{ij} = 1; \mathrm{outtree} \mid L_{\max}$ (minimal NP-hard in the strong sense, citing Timkovsky 2003).
- V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in scheduling complexity", European Journal of Operational Research 149 (2003), 355-376, doi:10.1016/S0377-2217(02)00767-1.
