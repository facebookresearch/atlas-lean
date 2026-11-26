# MULTIPROCESSOR TASKS $P2 \mid \mathrm{intree}; p_i = 1; \mathrm{size}_i \mid \sum C_i$ is NP-complete

The MULTIPROCESSOR TASKS $P2 \mid \mathrm{intree}; p_i = 1; \mathrm{size}_i \mid \sum C_i$ decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: two identical processors, each executing at most one task at a time; $n$ tasks, each with unit processing time ($p_i = 1$) and a size $\mathrm{size}_i \in \{1, 2\}$ (the task uses $\mathrm{size}_i$ processors, any of them, simultaneously); an in-tree precedence relation on the tasks (in-forest: each task has at most one immediate successor), where $i$ preceding $j$ means that $j$ cannot start before $i$ is completed; and a bound $K$. Question: is there a schedule, with natural-number start times, whose total completion time $\sum_i C_i$ is at most $K$, where $C_i$ is the completion time of task $i$?

## Sources

- Y. Zinder and V. H. Do, "Scheduling unit execution time tasks on two parallel machines with the criteria of makespan and total completion time", in G. Kendall, E. Burke, S. Petrovic and M. Gendreau (eds.), *Multidisciplinary Scheduling: Theory and Applications*, Springer (2005), 83-109, doi:10.1007/0-387-27744-7_5 (only the abstract was available).
- P. Brucker and S. Knust, *Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/, class pmpt_nop (multiprocessor tasks on parallel processors, without preemption), entry $P2 \mid \mathrm{intree}; p_i = 1; \mathrm{size}_i \mid \sum C_i$ (minimal NP-hard in the strong sense, citing Zinder and Do 2005).
