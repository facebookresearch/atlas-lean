# Threshold for minimum-weight decoding of the toric code

Suppose each edge of the $L \times L$ [toric code](toric-code.md) suffers a bit flip independently with probability $p$,
and the syndrome is measured perfectly. If $0 \le p < 1/2$ and $4\mu^2 p(1 - p) < 1$, which holds for $p < 0.0373$, where
$\mu \approx 2.638$ is the connective constant of self-avoiding walks on the square lattice (at most
$\mu^{\ell} e^{O(\sqrt{\ell})}$ of them start at a fixed vertex and have length $\ell$), then the probability that
[minimum-weight decoding](minimum-weight-decoding-of-the-toric-code.md) fails is at most
$e^{o(L)} \cdot (4\mu^2 p(1 - p))^{L/2}$, and so tends to $0$ exponentially in $L$. The restriction
$p < 1/2$ matters: at $p = 1$ the condition $4\mu^2 p(1 - p) < 1$ holds, yet for odd $L$ flipping every edge leaves an
empty syndrome and an odd winding in both directions, so decoding fails with certainty.

With faulty syndrome measurements, each readout wrong independently with probability $q$, and decoding by matching in the
spacetime syndrome history as described on the decoding page, the failure probability over a storage time $T$ is at most
$L^2 T \cdot e^{o(L)} \cdot (4\mu_3^2 \tilde p)^{L/2}$ when $\tilde p = \max(p(1 - p), q(1 - q)) < (4\mu_3^2)^{-1}$,
which holds for $p, q < 0.0114$; here $\mu_3 \approx 4.684$ is the connective constant of the cubic lattice. For $T$ at most
polynomial in $L$ this falls exponentially in $L$.

Dennis, Kitaev, Landahl and Preskill relate the threshold of the optimal decoder to a phase transition of the
random-bond Ising model and quote the numerical value $p_c \approx 0.1094$; that value is not a theorem.

## Expansion

A good expansion adds pages for the two steps of the proof: the bound on the probability that a given closed path of
length $\ell$ lies in $e + e'$ (Section V.B: at least half of its edges carry errors, giving $(4p(1 - p))^{\ell/2}$ up to
counting), and the count of self-avoiding walks of length $\ell$ from a fixed vertex of the square lattice, at most $\mu^{\ell} e^{O(\sqrt{\ell})}$
(a homologically nontrivial closed path on the torus lifts to an open walk, so walks rather than closed polygons
are counted, with $L^2$ starting vertices), together with the fact that a failure needs a homologically nontrivial path of
length at least $L$.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Proof depends on

- [The toric code has distance $L$](toric-code-has-distance-l.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V, equations (54)–(67) (stated there with a polynomial factor, from a count of closed polygons; the perfect-syndrome case in equations (65)–(67) and the faulty-syndrome case in equations (59)–(64)), and Section IV.F.
