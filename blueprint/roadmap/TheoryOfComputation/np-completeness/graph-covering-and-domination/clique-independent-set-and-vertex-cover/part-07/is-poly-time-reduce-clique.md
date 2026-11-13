# SAT ≤ CLIQUE is polynomial-time

Let $f$ be the map on bit strings that sends the
binary code of a CNF formula $\varphi$ to the encoding of Karp's CLIQUE instance $(k, G)$ of
$\varphi$, and sends every string that is not the code of a CNF formula to the string $100$.
Here $G$ has one vertex per literal occurrence in $\varphi$, two occurrences are adjacent when
they lie in different clauses and are not complementary, and $k$ is the number of clauses of
$\varphi$. Then $f$ is computable in polynomial time.
