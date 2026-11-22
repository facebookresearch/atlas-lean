# A timed decider with polynomial-time output function gives membership in P

Let $L$ be
a decision problem and let $f$ assign to each bit string $x$ a timed computation, that is, a
Boolean return value together with a declared time in $\mathbb{N}$, whose return value equals
$L(x)$ for every $x$. If the function sending $x$ to the return value of $f(x)$ is
polynomial-time computable, then $L$ belongs to the class P.

The polynomial-time hypothesis must be proved for the specific decider: it does not follow from a
polynomial bound on the declared times, which are trusted annotations, since every decision
problem has a decider of declared time zero.
