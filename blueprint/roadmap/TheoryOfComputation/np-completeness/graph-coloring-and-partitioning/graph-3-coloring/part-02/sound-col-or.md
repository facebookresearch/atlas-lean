# Output of the OR gadget under a proper 3-coloring

Let $c : \mathbb{N} \to \{0, 1, 2\}$
with $c(2) = 2$, let $a$ and $o$ be natural numbers, let $s$ be a state of the SAT-to-3-COLOR
construction and let $E$ be a list of pairs of natural numbers such that $c(u) \ne c(v)$ for
every pair $(u, v)$ in $E$. Apply the OR gadget to $a$, $o$ and $s$, giving a new state and an
output vertex $w$, and suppose every edge in the emitted-edge list of the new state belongs to
$E$. If $c(a) \ne 2$ and $c(o) \ne 2$, then $c(w) \ne 2$, and if $c(w) = 0$ then $c(a) = 0$ or
$c(o) = 0$.
