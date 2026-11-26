# Well-formed instances of 3SAT WITH AT MOST FIVE CLAUSES PER VARIABLE

An instance is a pair $(n, C)$: the variables are $0, \dots, n - 1$, and $C$ is a list of clauses, each clause a list of literals (a variable together with a sign). The instance is well-formed when

- every clause lists exactly three literals, no literal twice, and every literal is on a variable below $n$;
- for every variable $u < n$, at most five entries of the list $C$ are clauses containing a literal on $u$, positive or negative.

The bound counts clauses, not literal occurrences: a clause containing both $u$ and $\bar u$ counts once for $u$, while a clause that appears twice in the list counts twice. This differs from [3-SAT with bounded occurrences](../3-sat-with-bounded-occurrences/README.md), which bounds the number of literal occurrences of each variable.
