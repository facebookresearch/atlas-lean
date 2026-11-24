# Repeated passes reach a fixpoint

Let $n, s \in \mathbb{N}$ with $s < n$ and let $E$ be a
list of pairs of natural numbers. Let $r$ be the list obtained from the initial marks (only $s$
marked among $0, \dots, n - 1$) by $n$ marking passes of $E$ with bound $n$. Then one more
marking pass of $E$ with bound $n$ leaves $r$ unchanged.

Each pass that changes the marks adds at least one mark, the initial marks contain one mark, and
there are at most $n$ marks.
