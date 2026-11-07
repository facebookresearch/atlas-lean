# Completeness of the chain of one clause

Let $v$ and $v'$ be assignments with
$v'(2n) = v(n)$ for every $n$, let $C$ be a clause and $u$ a natural number, and write
$k = \mathrm{used}(C)$. Suppose that $v$ satisfies $C$, and that for every $w$ with
$u \le w < u + k$, $v'$ gives the fresh variable $\mathrm{fresh}(w)$ the value true exactly when
$v$ satisfies some literal of the clause obtained from $C$ by dropping its first $u + k - w$
literals. Then $v'$ satisfies every clause of $\mathrm{chain}(C, u)$.
