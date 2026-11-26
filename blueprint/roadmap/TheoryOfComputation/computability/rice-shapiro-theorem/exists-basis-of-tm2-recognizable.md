# Effective Rice–Shapiro, necessity

Let $C$ be a class of partial functions
$\mathbb{N} \rightharpoonup \mathbb{N}$ whose index set, the set of codes $c$ of partial
recursive functions such that the function computed by $c$ is in $C$, is recognizable. Then there
is a recognizable set $B$ of finite lists of pairs of natural numbers, each of which is a graph,
such that a partial recursive function $f$ is in $C$ if and only if some $\theta \in B$
satisfies: for every pair $(x, y)$ in $\theta$, $f(x)$ is defined and equals $y$.
