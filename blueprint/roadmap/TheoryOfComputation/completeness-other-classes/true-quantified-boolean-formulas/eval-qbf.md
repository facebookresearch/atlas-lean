# Evaluation of a quantified CNF formula

Let $\varphi$ be a CNF formula, let
$a : \mathbb{N} \to \{\mathrm{true}, \mathrm{false}\}$ be an assignment, and let $Q$ be a
quantifier prefix, a list of pairs $(e, v)$ of a flag $e$ (true for $\exists$, false for
$\forall$) and a variable $v \in \mathbb{N}$. Write $a[v \mapsto b]$ for the assignment that
agrees with $a$ except that it sends $v$ to $b$. With the empty prefix, the formula holds under
$a$ when $a$ satisfies $\varphi$. With a prefix whose first entry is $(e, v)$ and whose remaining
entries form $Q'$, it holds under $a$ when, if $e$ is true, the formula with prefix $Q'$ holds
under $a[v \mapsto \mathrm{true}]$ or under $a[v \mapsto \mathrm{false}]$, and, if $e$ is false,
the formula with prefix $Q'$ holds under both $a[v \mapsto \mathrm{true}]$ and
$a[v \mapsto \mathrm{false}]$.
