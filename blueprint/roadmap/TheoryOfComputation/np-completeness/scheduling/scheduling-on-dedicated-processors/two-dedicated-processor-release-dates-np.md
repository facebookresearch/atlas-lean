# TWO DEDICATED PROCESSORS WITH RELEASE DATES $P2 \mid r_i; \mathrm{fix}_i \mid C_{\max}$ is NP-complete

The TWO DEDICATED PROCESSORS WITH RELEASE DATES $P2 \mid r_i; \mathrm{fix}_i \mid C_{\max}$ decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: two processors $M_1$, $M_2$, each executing at most one task at a time; $n \ge 0$ tasks, task $i$ with a processing time $p_i \in \mathbb{Z}^+$, a nonempty set $\mathrm{fix}_i \subseteq \{M_1, M_2\}$ of processors that it uses simultaneously during its whole (uninterrupted) processing, and a release date $r_i \in \mathbb{Z}_0^+$ before which it cannot start; and a bound $K \in \mathbb{N}$. Tasks whose processor sets intersect cannot overlap in time. Question: is there a schedule with natural-number start times in which every task completes by time $K$? When $n \ge 1$, this says that the makespan $\max_i C_i$ is at most $K$, where $C_i$ is the completion time of task $i$; when $n = 0$, every bound $K$ gives a yes-instance.

## Sources

- J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272, doi:10.1016/0166-218X(94)90012-4, Theorem 2.8.
- P. Brucker and S. Knust, *Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/, class mpt (multiprocessor tasks), entry $P2 \mid r_i; \mathrm{fix}_i \mid C_{\max}$ (minimal NP-hard in the strong sense, citing Hoogeveen et al. 1994).
