# Completeness of the auxiliary 3SAT translation

Let $v, v' : \mathbb{N} \to \mathrm{Bool}$
be assignments with $v'(2n) = v(n)$ for every $n$, let $\varphi$ be a CNF formula satisfied by
$v$, and let $N$ be the next free fresh number of the auxiliary SAT-to-3SAT translation of
$\varphi$. If for every $w < N$ the assignment $v'$ gives fresh variable number $w$, the variable
$2^{w+1} + 1$, the fresh-variable value of $w$ built from $v$ and $\varphi$, then $v'$ satisfies
the clause list produced by the auxiliary translation of $\varphi$.
