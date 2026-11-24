# Quadratic run of the padding machine on canonical instances

For every list $a = (a_1, \dots, a_n)$ of natural numbers and every natural number $t$, let $x$
be the encoding of the SUBSET-SUM instance with numbers $a$ and target $t$. The
[padding machine](prog-3.md) started at $\mathsf{target}$ with internal state false, with $x$ on
$X$ and every other stack empty, reaches $\mathsf{done}$ in at most $20(|x| + 1)^2$ steps, with
some internal state and stack contents in which $O$ holds the canonical encoding of the
[padded instance](from-subset-sum.md) $(a_1 + \dots + a_n, 2t, a_1, \dots, a_n)$. This includes
the case $t > a_1 + \dots + a_n$.
