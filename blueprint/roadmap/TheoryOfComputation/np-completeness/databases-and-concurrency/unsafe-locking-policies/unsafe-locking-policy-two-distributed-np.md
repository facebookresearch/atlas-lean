# UNSAFE LOCKING POLICY for two distributed transactions is NP-complete

The UNSAFE LOCKING POLICY for two distributed transactions decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a set of variables partitioned into sites, and two transactions `T₀`, `T₁`, each a partially ordered set of steps `lock(x)`, `update(x)`, `unlock(x)` in which the steps involving variables of any one site are totally ordered, and which, read in that order, satisfies the conditions of UNSAFE LOCKING POLICY (each `update(x)` between a `lock(x)`-`unlock(x)` pair, at most one such pair per variable). Any number of sites may be involved in each transaction. Question: is there a legal schedule that is a total order of all the steps, consistent with the partial orders of both transactions, and that is not serializable?

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300, doi:10.1016/0196-6774(83)90028-7, Section 3, the distributed model preceding problem [8] and the remark that UNSAFE LOCKING POLICY (problem [6]), restricted to total-order schedules, "becomes NP-complete if an arbitrary number of sites is allowed in each transaction" for two transactions.
- P. C. Kanellakis and C. H. Papadimitriou, "Is distributed locking harder?", J. Comput. System Sci. 28 (1984), 103-120, doi:10.1016/0022-0000(84)90078-3 (conference version: Proc. 1st ACM SIGACT-SIGMOD Symp. on Principles of Database Systems (1982), 98-107, doi:10.1145/588111.588129).
