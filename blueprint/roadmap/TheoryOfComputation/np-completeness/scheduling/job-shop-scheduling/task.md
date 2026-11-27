# Tasks of an instance of JOB-SHOP SCHEDULING

An instance of JOB-SHOP SCHEDULING is a triple $(m, J, D)$ of a number $m$ of processors, a list $J$ of jobs, and a deadline $D$; job $j$, at position $j$ of $J$, is the list of its tasks $t_1[j], \dots, t_{n_j}[j]$ in order, each task given as the pair $(l(t), p(t))$ of its length and its processor, all natural numbers. A task of the instance is a pair $(j, k)$ of a job $j$, a position of $J$, and a position $k \in \{0, \dots, n_j - 1\}$ in the task list of job $j$; positions are numbered from $0$, so $(j, k)$ is the task $t_{k+1}[j]$.
