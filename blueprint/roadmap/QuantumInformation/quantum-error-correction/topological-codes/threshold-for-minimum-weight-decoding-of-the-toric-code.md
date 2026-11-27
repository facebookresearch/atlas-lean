# Threshold for minimum-weight decoding of the toric code

Suppose each edge of the $L \times L$ [toric code](toric-code.md) suffers a bit flip independently with probability $p$,
and the syndrome is measured perfectly. If $0 \le p < 1/2$ and $4\mu^2 p(1 - p) < 1$, where
$\mu$ is the connective constant of self-avoiding walks on the square lattice (at most
$\mu^{\ell} e^{O(\sqrt{\ell})}$ of them start at a fixed vertex and have length $\ell$), then the probability that
[minimum-weight decoding](minimum-weight-decoding-of-the-toric-code.md) fails is at most
$e^{o(L)} \cdot (4\mu^2 p(1 - p))^{L/2}$, and so tends to $0$ exponentially in $L$. The restriction
$p < 1/2$ matters: at $p = 1$ the condition $4\mu^2 p(1 - p) < 1$ holds, yet for odd $L$ flipping every edge leaves an
empty syndrome and an odd winding in both directions, so decoding fails with certainty. With the
estimate $\mu \approx 2.638$ that Dennis, Kitaev, Landahl and Preskill quote, the condition reads $p < 0.0373$; this
decimal is an estimate, not a certified bound; it would follow from a certified bound $\mu < 2.6385$.

Dennis, Kitaev, Landahl and Preskill relate the threshold of the optimal decoder to a phase transition of the
random-bond Ising model and quote the numerical value $p_c \approx 0.1094$; that value is not a theorem.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)
- [Counting self-avoiding walks on the square lattice](counting-self-avoiding-walks-on-the-square-lattice.md)

## Proof depends on

- [The probability that a fixed cycle lies in the error plus the correction](probability-that-a-fixed-cycle-lies-in-the-error-plus-the-correction.md)
- [Minimum-weight decoding fails only on a homologically nontrivial cycle](minimum-weight-decoding-fails-only-on-a-nontrivial-cycle.md)
- [The toric code has distance $L$](toric-code-has-distance-l.md)

## Related topics

- [Threshold for toric-code decoding with faulty syndrome measurements](threshold-for-toric-code-decoding-with-faulty-syndrome-measurements.md): the case of faulty syndrome measurements.

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V, equations (54)–(67) (the constants (57)–(58) and the decimals (63)–(67) are approximate; the bounds are stated there with a polynomial factor, from a count of closed polygons; the perfect-syndrome case in equations (65)–(67) and the faulty-syndrome case in equations (59)–(64)), and Section IV.F.
