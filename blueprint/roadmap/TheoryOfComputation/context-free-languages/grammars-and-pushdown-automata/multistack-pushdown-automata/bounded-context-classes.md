# Context-, round-, phase- and scope-bounded runs

For a sequence of MPDA transitions: a **context** is a maximal factor in which only one stack is accessed (pushes and pops of a single stack); a **round** is a factor $\tau_1\cdots\tau_n$ in which each $\tau_s$, possibly empty, accesses only stack $s$ (so a round has at most $n$ contexts); a **phase** is a maximal factor in which only one stack is popped. The sequence is $K$-**context-bounded** if it has at most $K$ contexts, $K$-**round-bounded** if it is a concatenation of at most $K$ rounds, $K$-**phase-bounded** if it has at most $K$ phases, and $K$-**scope-bounded** if every matched push and pop are separated by at most $K$ context switches. $K$ rounds give at most $Kn$ contexts, and $K$ contexts imply $K$-scope-boundedness.

## Depends on

- [Multistack pushdown automata](multistack-pushdown-automata.md)
- [Well-nested sequences and matching of push/pop transitions](well-nested-transition-sequences.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020.
