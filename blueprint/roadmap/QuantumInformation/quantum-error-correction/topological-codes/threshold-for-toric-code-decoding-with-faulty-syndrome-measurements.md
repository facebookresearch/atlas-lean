# Threshold for toric-code decoding with faulty syndrome measurements

Suppose each edge of the $L \times L$ [toric code](toric-code.md) suffers a bit flip independently with probability $p$ in
each round of syndrome measurement, and each syndrome readout is wrong independently with probability $q$. Assume, as
Dennis, Kitaev, Landahl and Preskill do, that the complete syndrome history is known, with measurements repeated
indefinitely, and decode by the weighted minimal chain of the
[minimum-weight decoding page](minimum-weight-decoding-of-the-toric-code.md): space-like edges stand for data errors and
time-like edges for readout errors, with weights $\log((1 - p)/p)$ and $\log((1 - q)/q)$, and edges of a type whose rate is
$0$ are not used. Decoding fails when the error chain plus the chosen chain contains a cycle that is homologically
nontrivial in the spatial directions. If $0 \le p, q < 1/2$ and $p(1 - p), q(1 - q) < (4\mu_3^2)^{-1}$, where $\mu_3$ is the
connective constant of self-avoiding walks on the cubic lattice, then the probability that such a cycle passes through a
given window of $T$ consecutive rounds is at most $L^2 T \cdot e^{o(L)} \cdot (4\mu_3^2\, p(1 - p))^{L/2}$. For $T$ at most
polynomial in $L$ this falls exponentially in $L$. With the estimate $\mu_3 \approx 4.684$ that Dennis, Kitaev, Landahl and
Preskill quote, the conditions read $p, q < 0.0114$; that decimal is an estimate, not a certified bound (it would need
$\mu_3 < 4.7098$). A decoder that sees only a finite record of rounds needs its own rule at the last round, where a single
wrong readout leaves an unpaired change; this page does not cover it.

## Expansion

A good expansion adds the spacetime versions of the three steps of the
[perfect-syndrome threshold](threshold-for-minimum-weight-decoding-of-the-toric-code.md): the decoder fails only if the
error history plus the correction contains a self-avoiding path in the spacetime lattice of length at least $L$ that is
homologically nontrivial in the spatial directions; such a fixed path with $H$ space-like and $V$ time-like edges lies in
the error plus the correction with probability at most $(4p(1 - p))^{H/2} (4q(1 - q))^{V/2}$, because the minimality is
for the weighted length, so the error edges on the path carry at least half of its weight; and the count of
self-avoiding walks from a fixed vertex of the cubic lattice, at most $\mu_3^{\ell} e^{o(\ell)}$, with $L^2 T$ starting
vertices.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Related topics

- [Threshold for minimum-weight decoding of the toric code](threshold-for-minimum-weight-decoding-of-the-toric-code.md): the case of perfect syndrome measurements.

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.A, equations (44)–(46) (the weights), Section V.B, equations (47)–(55) (the weighted bound on a fixed path and the failure bound), Section V.C, equations (58)–(64) (the cubic-lattice count; the constant (58) and the decimals (63)–(64) are approximate, and the bound is stated there with a polynomial factor from a count of closed polygons), and the opening of Section VI (the complete syndrome history assumed in Section V).
