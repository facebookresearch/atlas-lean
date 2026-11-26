# Scope-bounded and round-bounded runs are hole-bounded

For every MPDA with $n$ stacks and every complete run (empty stacks at both ends): if every push and its matching pop are separated by at most $K$ context switches, the label sequence is $K$-hole-bounded; if the sequence has at most $K$ rounds, it is $Kn$-hole-bounded. In particular context-bounded runs are hole-bounded.

## Proof sketch

Each hole at a prefix must have been opened in a distinct context that is still within the scope of its pending pushes; there are at most $K$ such contexts. Rounds yield at most $Kn$ contexts.

## Depends on

- [Holes and hole-bounded sequences](hole-bounded-sequences.md)
- [Context-, round-, phase- and scope-bounded runs](bounded-context-classes.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020, Proposition 2.
