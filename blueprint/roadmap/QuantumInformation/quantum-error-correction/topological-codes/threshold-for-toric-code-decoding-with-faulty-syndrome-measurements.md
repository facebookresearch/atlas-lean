# Threshold for toric-code decoding with faulty syndrome measurements

Suppose each edge of the $L \times L$ [toric code](toric-code.md) suffers a bit flip independently with probability $p$ in
each of $T$ rounds of syndrome measurement, and each syndrome readout is wrong independently with probability $q$. Decode
by matching in the spacetime syndrome history, as on the
[minimum-weight decoding page](minimum-weight-decoding-of-the-toric-code.md): space-like edges stand for data errors and
time-like edges for readout errors, with weights $\log((1 - p)/p)$ and $\log((1 - q)/q)$. If $0 \le p, q < 1/2$ and
$\tilde p = \max(p(1 - p), q(1 - q)) < (4\mu_3^2)^{-1}$, which holds for $p, q < 0.0114$, where $\mu_3 \approx 4.684$ is the
connective constant of self-avoiding walks on the cubic lattice, then the probability that decoding fails over the $T$
rounds is at most $L^2 T \cdot e^{o(L)} \cdot (4\mu_3^2 \tilde p)^{L/2}$. For $T$ at most polynomial in $L$ this falls
exponentially in $L$.

## Expansion

A good expansion adds the spacetime versions of the three steps of the
[perfect-syndrome threshold](threshold-for-minimum-weight-decoding-of-the-toric-code.md): the decoder fails only if the
error history plus the correction contains a self-avoiding path in the spacetime lattice of length at least $L$ that is
homologically nontrivial in the spatial directions; such a fixed path with $H$ space-like and $V$ time-like edges lies in
the error plus the correction with probability at most $(4p(1 - p))^{H/2} (4q(1 - q))^{V/2}$; and the count of
self-avoiding walks from a fixed vertex of the cubic lattice, at most $\mu_3^{\ell} e^{o(\ell)}$, with $L^2 T$ starting
vertices.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Related topics

- [Threshold for minimum-weight decoding of the toric code](threshold-for-minimum-weight-decoding-of-the-toric-code.md): the case of perfect syndrome measurements.

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section IV, equations (44)–(46) (the syndrome history and the weights), and Section V, equations (55) and (58)–(64) (the failure bound with the cubic-lattice count, stated there with a polynomial factor from a count of closed polygons).
