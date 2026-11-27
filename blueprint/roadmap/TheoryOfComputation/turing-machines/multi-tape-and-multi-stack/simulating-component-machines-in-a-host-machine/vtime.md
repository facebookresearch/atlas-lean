# Step bound of the verifier host

Let $c$ be a component machine with stacks $c_X$ and
$c_W$, encodings $g_X$ and $g_W$ of bits as symbols of $c_X$ and $c_W$, and labels
$\mathit{start}$, $\mathit{yes}$ and $\mathit{no}$, and let $B$ be the push bound of the verifier
host machine built from these data. For a polynomial $p$ with natural-number coefficients, the
step bound of the verifier host is the polynomial in the variable $X$

$$(B + 1)(2X + 4 + p) + X + 2.$$

At an input length $n$ it counts phase 0 and the component, at most $2n + 4 + p(n)$ steps, then
the cleanup, which takes at most one step more than the longest stack, of length at most $n$
plus $B$ times the steps so far, and the output step.
