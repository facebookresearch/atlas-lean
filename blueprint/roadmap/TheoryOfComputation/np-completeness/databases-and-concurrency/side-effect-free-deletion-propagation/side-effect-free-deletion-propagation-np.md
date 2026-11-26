# SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view) is NP-complete

The SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view) decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a source database, that is, finite relations $R_1$ over $(A, B)$ and $R_2$ over $(B, C)$ with natural-number values, and a tuple $t$ of the view $V(R_1, R_2) = \Pi_{A,C}(R_1 \bowtie R_2)$. Question: is there a set of source tuples $T_1 \subseteq R_1$, $T_2 \subseteq R_2$ whose deletion is side-effect-free: it removes $t$ from the view and no other view tuple, that is, $V(R_1 \setminus T_1, R_2 \setminus T_2) = V(R_1, R_2) \setminus \{t\}$?

## Sources

- P. Buneman, S. Khanna and W.-C. Tan, "On propagation of deletions and annotations through views", Proceedings of the 21st ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS 2002), 150-158, doi:10.1145/543613.543633 (Section 2.1.1, Theorem 2.1: deciding whether there is a side-effect-free deletion is NP-hard for the project-join query $\Pi_{A,C}(R_1(A, B) \bowtie R_2(B, C))$).
