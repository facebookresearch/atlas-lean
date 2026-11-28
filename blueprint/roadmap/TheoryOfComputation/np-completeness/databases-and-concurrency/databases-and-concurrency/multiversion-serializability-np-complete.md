# MULTIVERSION SERIALIZABILITY is NP-complete

The decision problem MULTIVERSION SERIALIZABILITY belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300, doi:10.1016/0196-6774(83)90028-7, problem [5] MULTIVERSION SERIALIZABILITY (the problem, credited to Papadimitriou and Kanellakis, transformation from POLYGRAPH ACYCLICITY).
- C. H. Papadimitriou and P. C. Kanellakis, "On concurrency control by multiple versions", Proc. 1st ACM SIGACT-SIGMOD Symp. on Principles of Database Systems (1982), 76-82, doi:10.1145/588111.588125, and ACM Trans. Database Systems 9 (1984), 89-99, doi:10.1145/348.318588.
- C. H. Papadimitriou, "The serializability of concurrent database updates", J. ACM 26 (1979), 631-653, doi:10.1145/322154.322158 (the semantics of schedules: written values are uninterpreted functions of the values the transaction read at earlier steps, and two schedules are equivalent when they leave the same final values under every interpretation).
