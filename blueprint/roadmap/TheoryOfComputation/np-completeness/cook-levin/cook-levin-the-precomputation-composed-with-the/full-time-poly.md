# Polynomial time bound of the composed machine

Let $M$ be a finite multi-stack machine
with encoding data $E$, let $Y$ be a list of symbols of the input stack of $M$, $a$ a symbol of
its output stack, $\iota$ a map from the raw symbols $\mathrm{Fin}\,r$ to symbols of the input
stack, $\sigma$ a symbol of the input stack (the separator), $k$ a polynomial with
natural-number coefficients and $c, e \in \mathbb{N}$. Then there is a polynomial $p$ with
natural-number coefficients such that the following holds for every raw input
$s = s_1 \cdots s_n$ over $\mathrm{Fin}\,r$ and every list $o$ of booleans. Write
$m = n + 1 + k(n)$, $T = (m + c)^e$ and $x = \iota(s_1) \cdots \iota(s_n)\,\sigma$. The full
program on the real generators for $E$, $Y$, $a$, $\iota$, $\sigma$, $k$, $c$ and $e$, started at
its read-loop label with flag false, $s$ on the raw input stack, $o$ on the host output stack and
every other stack empty, reaches the host's final label within $p(n)$ steps, with some flag and
some stack contents in which the host output stack holds the dense encoding of the formula
$\Phi(x, Y, a, m, T)$ emitted by the host, followed by $o$.
