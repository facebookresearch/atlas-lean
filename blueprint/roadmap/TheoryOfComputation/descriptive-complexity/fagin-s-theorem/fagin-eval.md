# Evaluation of a first-order formula in a graph

Let $G$ be a graph, let $\rho$ assign a
vertex $\rho(j)$ of $G$ to each variable $x_j$ ($j \in \mathbb{N}$), and let $S$ assign to each
relation symbol $i \in \mathbb{N}$ a predicate $S_i$ on finite lists of vertices of $G$. Truth of a
formula is defined by recursion: $x_a = x_b$ holds when $\rho(a) = \rho(b)$; relation symbol $i$
applied to the variables $x_{a_1}, \dots, x_{a_m}$ holds when $S_i$ holds of the list
$[\rho(a_1), \dots, \rho(a_m)]$; negation, conjunction and disjunction are interpreted as usual;
and $\exists \varphi$ holds when there is a vertex $v$ such that $\varphi$ holds under the
assignment sending $x_0$ to $v$ and $x_{j+1}$ to $\rho(j)$ for each $j$, with $S$ unchanged.
