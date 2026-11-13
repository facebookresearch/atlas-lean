# Fagin's theorem: NP is existential second-order logic

Let $K$ be a class of finite
graphs, each given as a pair $(n, t)$ of a number $n$ of vertices and a row-major edge table $t$
(a list of booleans), and suppose that $K$ is closed under graph isomorphism. Then the decision
problem that accepts exactly the bitstrings decoding to a member $(n, t)$ of $K$ whose edge table
has length $n^2$ is in NP if and only if $K$ is definable in existential second-order logic:
there are a first-order formula $\varphi$, a number $k$ and a boolean $b$ such that a graph
$(n, t)$ whose edge table has length $n^2$ belongs to $K$ exactly when either $n > 0$ and some
$k$ relations on its vertices, together with its edge relation, make $\varphi$ true (with every
free variable of $\varphi$ denoting vertex $0$), or $n = 0$ and $b$ is true.

## Sources

- R. Fagin, "Generalized first-order spectra and polynomial-time recognizable sets", in Complexity of Computation, SIAM-AMS Proceedings 7 (1974), 43-73.
