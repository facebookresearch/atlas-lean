# MULTIWAY NUMBER PARTITION is NP-complete

Let MULTIWAY NUMBER PARTITION be the decision
problem that accepts exactly the bitstrings decoding to a feasible multiway number partition
instance: a list of natural numbers and a number $K \ge 1$ such that the entries of the list,
counted with repetition, can be split into $K$ nonempty parts with equal sums. Then MULTIWAY
NUMBER PARTITION is in NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

For $K = 2$ this is PARTITION restricted to splits into two nonempty parts: the one-entry list
$(0)$, for instance, is a yes-instance of PARTITION but has no split into two nonempty parts.

## Sources

- Michael R. Garey and David S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman, 1979 (PARTITION [SP12]).
