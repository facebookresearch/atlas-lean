# Equivalence test

Over a finite alphabet with decidable equality and a fixed enumeration of
its letters, the equivalence test of two encoded regular expressions $e_1$ and $e_2$ returns true
exactly when, for every length $n$ less than the search bound of $e_1$ and $e_2$ and every word $w$
of length $n$, the membership test gives the same answer for $e_1$ on $w$ as for $e_2$ on $w$.
