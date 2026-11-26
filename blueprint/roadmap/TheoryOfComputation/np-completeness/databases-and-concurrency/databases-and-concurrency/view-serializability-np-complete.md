# VIEW SERIALIZABILITY is NP-complete

Given a schedule of read and write actions of single variables by $n$ transactions, decide whether some serial schedule of the same transactions agrees with it on every final value and on the value of every read. This problem is in NP, and every NP problem reduces to it by a polynomial-time many-one reduction.

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300, Section 3.
- M. Yannakakis, "Serializability by locking", J. ACM 31 (1984), 227-244.
- C. H. Papadimitriou, "The serializability of concurrent database updates", J. ACM 26 (1979), 631-653.
