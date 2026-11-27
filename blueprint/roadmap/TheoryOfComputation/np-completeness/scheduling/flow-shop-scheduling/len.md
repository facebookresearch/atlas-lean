# Task lengths in FLOW-SHOP SCHEDULING

An instance of FLOW-SHOP SCHEDULING is a triple $(m, T, D)$ of a number $m$ of processors, a list $T$ of lists of natural numbers, one list per job, and a deadline $D$; the jobs are the positions $0, \dots, |T|-1$ of $T$ and the processors are $0, \dots, m-1$. The length $l(t_p[j])$ of the task of job $j$ on processor $p$ is the entry at position $p$ of the list at position $j$ of $T$, and $0$ when that list has no entry at position $p$. That every job has exactly $m$ task lengths is a condition of a well-formed instance, not of this definition.
