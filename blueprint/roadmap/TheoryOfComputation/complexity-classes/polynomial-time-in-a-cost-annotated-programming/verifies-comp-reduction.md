# Pulling a verifier back along a declared reduction

Let $L_1$ and $L_2$ be decision
problems, let $f$ be a declared polynomial-time many-one reduction from $L_1$ to $L_2$, and let
$V$ be a verifier with polynomial declared time that verifies $L_2$ with witness bound $p$. Let
$V'$ be the verifier that on input $x$ and witness $w$ first runs $f$ on $x$, obtaining $y$, then
runs $V$ on $(y, w)$ and accepts when $V$ accepts and $|w| \le p(|y|)$; its declared time is the
declared time of $f(x)$ plus that of $V(y, w)$. Then $V'$ has polynomial declared time, and there
is a polynomial $p'$ with natural coefficients such that $V'$ verifies $L_1$ with witness bound
$p'$.

The proof takes $p' = p \circ r$ and the time bound $r(n) + q(r(n) + n)$ with $n = |x| + |w|$,
where $r$ bounds the declared time and output length of $f$ and $q$ bounds the declared time of
$V$.
