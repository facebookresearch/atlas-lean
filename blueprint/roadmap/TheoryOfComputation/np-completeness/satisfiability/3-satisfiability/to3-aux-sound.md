# Soundness of the auxiliary 3SAT translation

For every assignment
$v' : \mathbb{N} \to \mathrm{Bool}$ and every CNF formula $\varphi$, if $v'$ satisfies the
clause list produced by the auxiliary SAT-to-3SAT translation of $\varphi$, then the assignment
$n \mapsto v'(2n)$ satisfies $\varphi$.
