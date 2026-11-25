# MULTIPROCESSOR TASKS `P2|outtree;p_i=1;size_i|ΣC_i` is NP-complete

The MULTIPROCESSOR TASKS `P2|outtree;p_i=1;size_i|ΣC_i` decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: two identical processors, each executing at most one task at a time; `n` tasks, each with unit processing time (`p_i = 1`) and a size `size_i ∈ {1, 2}` (the task uses `size_i` processors, any of them, simultaneously); an out-tree precedence relation on the tasks (out-forest: each task has at most one immediate predecessor), where `i` preceding `j` means that `j` cannot start before `i` is completed; and a bound `K`. Question: is there a schedule whose total completion time `ΣC_i` is at most `K`, where `C_i` is the completion time of task `i`?

## Sources

- Y. Zinder, V. H. Do and C. Oğuz, "Computational complexity of some scheduling problems with multiprocessor tasks", Discrete Optimization 2 (2005), 391-408, doi:10.1016/j.disopt.2005.08.001, Section 3.
- P. Brucker and S. Knust, *Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on parallel processors, without preemption), entry `P2|outtree;p_i=1;size_i|ΣC_i` (minimal NP-hard in the strong sense, citing Zinder, Do and Oğuz 2005).
