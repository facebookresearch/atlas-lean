# Karp's reduction from SAT to CLIQUE is correct

A CNF formula $\varphi$ with $m$ clauses is
satisfiable if and only if Karp's graph of $\varphi$ has a clique of exactly $m$ vertices. Karp's
graph has one vertex for each literal occurrence of $\varphi$, and two occurrences are adjacent
when they lie in different clauses and are not complementary.
