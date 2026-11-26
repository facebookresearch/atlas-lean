# The probability that a fixed cycle lies in the error plus the correction

Let each edge of the $L \times L$ [toric code](toric-code.md) carry a bit flip independently with probability
$p < 1/2$, let $E$ be the set of flipped edges and $E_{\min}$ the correction chosen by
[minimum-weight decoding](minimum-weight-decoding-of-the-toric-code.md), a set of fewest edges with the same boundary
as $E$. For a fixed self-avoiding closed path $\gamma$ of $\ell$ edges,

$$\Pr\big[\gamma \subseteq E + E_{\min}\big] \le 2^{\ell} \big( p (1 - p) \big)^{\ell/2} = \big( 4 p (1 - p) \big)^{\ell/2} .$$

If $\gamma \subseteq E + E_{\min}$, each edge of $\gamma$ lies in exactly one of $E$ and $E_{\min}$; the edges of
$\gamma \cap E$ and of $\gamma \cap E_{\min}$ have the same boundary, so minimality of $E_{\min}$ forces
$|\gamma \cap E| \ge \ell / 2$. There are at most $2^{\ell}$ ways to split $\gamma$, and each split with $e \ge \ell/2$
error edges on $\gamma$ has probability at most $p^{e} (1 - p)^{\ell - e} \le (p(1 - p))^{\ell/2}$ of being realized.
With noisy syndrome measurements the same argument on the three-dimensional spacetime lattice gives
$2^{H + V} \tilde p^{H/2} \tilde q^{V/2}$ with $\tilde p = p(1 - p)$, $\tilde q = q(1 - q)$.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.B, equations (47)–(53).
