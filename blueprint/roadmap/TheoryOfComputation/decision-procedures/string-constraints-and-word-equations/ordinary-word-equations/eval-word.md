# Substitution of words for variables in a word

Let $\alpha$ be an alphabet of constants and $V$ a set of variables. For a substitution $\sigma : V \to
\alpha^*$ and a finite word $w = c_1 \cdots c_k$ over $\alpha \cup V$ (disjoint union), the evaluation
$\sigma(w)$ is the concatenation $u_1 \cdots u_k$, where $u_j$ is the one-letter word $c_j$ if $c_j \in
\alpha$ and $u_j = \sigma(c_j)$ if $c_j \in V$.
