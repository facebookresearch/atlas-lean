# The Cook–Levin reduction

Let $V$ be a polynomial-time Turing machine that computes a
Boolean function on pairs of bit strings, reading a pair $(a, y)$ as the bits of $a$, a separator,
then the bits of $y$, and writing its answer as one bit; let $t$ be its time bound and fix
constants $c \ge 1$ and $e$ with $t(j) \le (j + c)^e$ for all $j$. For a polynomial $p$ with
natural-number coefficients, the reduction sends a bit string $a$ of length $n$ to the dense bit
encoding of the tableau formula $\Phi$ of $V$, built with the encoding of $V$ whose output
alphabet contains the output symbol $\mathrm{acc}$ for true, for the input prefix $x$ made of the
bits of $a$ followed by the separator, the certificate symbols of $V$ (one per bit) as the
allowed symbols after $x$, the accept symbol $\mathrm{acc}$, width $m = n + 1 + p(n)$ and
$T = (m + c)^e$ steps.
