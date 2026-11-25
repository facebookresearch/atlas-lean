# MULTIPROCESSOR TASKS `P2|intree;p_i=1;size_i|ΣC_i` is NP-complete

The MULTIPROCESSOR TASKS `P2|intree;p_i=1;size_i|ΣC_i` decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: two identical processors, each executing at most one task at a time; `n` tasks, each with unit processing time (`p_i = 1`) and a size `size_i ∈ {1, 2}` (the task uses `size_i` processors, any of them, simultaneously); an in-tree precedence relation on the tasks (in-forest: each task has at most one immediate successor), where `i` preceding `j` means that `j` cannot start before `i` is completed; and a bound `K`. Question: is there a schedule whose total completion time `ΣC_i` is at most `K`, where `C_i` is the completion time of task `i`?

## Sources

- Y. Zinder and V. H. Do, "Scheduling unit execution time tasks on two parallel machines with the criteria of makespan and total completion time", in G. Kendall, E. Burke, S. Petrovic and M. Gendreau (eds.), *Multidisciplinary Scheduling: Theory and Applications*, Springer (2005), 83-112, doi:10.1007/0-387-27744-7_5 (only the abstract was available).
- P. Brucker and S. Knust, *Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on parallel processors, without preemption), entry `P2|intree;p_i=1;size_i|ΣC_i` (minimal NP-hard in the strong sense, citing Zinder and Do 2005).
