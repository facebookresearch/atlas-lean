# The answer machine runs in one step

Let $M$ be a finite multi-stack machine with finite
stack alphabets, whose input alphabet is identified with the bits by $e$ and whose output alphabet
by $e_1$. For every non-blank cell $x$ of the single-tape emulation alphabet of $M$, the answer
machine of $M$, started on the one-cell tape $x$, halts within at most one step on the one-cell
tape holding the input-bit cell of the answer of $x$ (the bit telling whether $x$ holds
$e_1^{-1}(\mathrm{true})$ on the output stack).
