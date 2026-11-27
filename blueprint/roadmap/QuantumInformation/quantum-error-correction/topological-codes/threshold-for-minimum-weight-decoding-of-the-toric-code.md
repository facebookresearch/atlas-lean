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

With faulty syndrome measurements, take the finite record of the
[decoding page](minimum-weight-decoding-of-the-toric-code.md): $T$ noisy rounds with data error rate $p$ and readout error
rate $q$, followed by one error-free round, decoded by a chain of least weighted length with boundary the detection
events. Decoding fails when the residual chain $E + E'$ has a nonzero total spatial homology class. This event is
contained in the larger event that $E + E'$ contains a self-avoiding closed path that is homologically nontrivial in the
spatial directions, and that larger event is what the counting bounds. If $0 \le p, q < 1/2$ and
$p(1 - p), q(1 - q) < (4\mu_3^2)^{-1}$, where $\mu_3$ is the connective constant of self-avoiding walks on the cubic lattice,
its probability is at most $L^2 (T + 1) \cdot e^{o(L)} \cdot (4\mu_3^2\, p(1 - p))^{L/2}$, which for $T$ at most polynomial in
$L$ falls exponentially in $L$. With the estimate $\mu_3 \approx 4.684$ the conditions read $p, q < 0.0114$, again an estimate rather than a certified bound (it would need $\mu_3 < 4.7098$).

Dennis, Kitaev, Landahl and Preskill relate the threshold of the optimal decoder to a phase transition of the
random-bond Ising model and quote the numerical value $p_c \approx 0.1094$; that value is not a theorem.

## Expansion

A good expansion adds pages for the two steps of the proof: the bound on the probability that a given closed path of
length $\ell$ lies in $e + e'$ (Section V.B: at least half of its edges carry errors, giving $(4p(1 - p))^{\ell/2}$ up to
counting; with faulty measurements the minimality is for the weighted length, so the error edges on a path with $H$
space-like and $V$ time-like edges carry at least half of its weight, which gives $(4p(1 - p))^{H/2} (4q(1 - q))^{V/2}$,
equations (47)–(52)), and the count of self-avoiding walks of length $\ell$ from a fixed vertex of the square lattice, at most $\mu^{\ell} e^{O(\sqrt{\ell})}$
(a homologically nontrivial closed path on the torus lifts to an open walk, so walks rather than closed polygons
are counted, with $L^2$ starting vertices), together with the fact that a failure needs a homologically nontrivial path of
length at least $L$. With faulty measurements the argument runs in the finite spacetime slab of the record, whose
$L^2 (T + 1)$ vertices are the starting points; Dennis, Kitaev, Landahl and Preskill state it for the complete history,
counting walks between two time slices, and the expansion checks that equations (47)–(55) apply unchanged in the slab.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Proof depends on

- [The toric code has distance $L$](toric-code-has-distance-l.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V, equations (54)–(67) (the constants (57)–(58) and the decimals (63)–(67) are approximate; the bounds are stated there with a polynomial factor, from a count of closed polygons; the perfect-syndrome case in equations (65)–(67) and the faulty-syndrome case in equations (59)–(64)), and Section IV.F.
