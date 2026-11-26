# The effective Rice–Shapiro theorem

Let $C$ be a class of partial functions from $\mathbb{N}$ to $\mathbb{N}$. The index set of $C$ (the
set of codes $c$ of partial recursive functions whose function belongs to $C$) is recognizable by a
multi-stack Turing machine if and only if there is a predicate $B$ on finite lists of pairs of
natural numbers such that $B$ is recognizable by a multi-stack Turing machine, every list $\theta$
with $B(\theta)$ is the graph of a function (each listed pair $(x, y)$ has $y$ equal to the first
value listed at $x$), and for every partial recursive $f$: $f \in C$ if and only if some $\theta$
with $B(\theta)$ satisfies $f(x) = y$ for every pair $(x, y)$ in $\theta$.
