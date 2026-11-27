# Threshold for toric-code decoding with faulty syndrome measurements

Take the finite record of the [minimum-weight decoding page](minimum-weight-decoding-of-the-toric-code.md) on the
$L \times L$ [toric code](toric-code.md): starting from a code state with no errors, $T$ rounds in which each edge suffers a
bit flip independently with probability $p$ before the round and each syndrome readout is wrong independently with
probability $q$, followed by one error-free round. Decode by a chain $E'$ of least weighted length whose boundary is the
set of detection events, with weights $\log((1 - p)/p)$ for space-like and $\log((1 - q)/q)$ for time-like edges, edges of a
type whose rate is $0$ not being used. Decoding fails when the residual chain $E + E'$ has a nonzero total spatial
homology class. If $0 \le p, q < 1/2$ and $p(1 - p), q(1 - q) < (4\mu_3^2)^{-1}$, where $\mu_3$ is the connective constant of
self-avoiding walks on the cubic lattice, the probability of failure is at most
$L^2 (T + 1) \cdot e^{o(L)} \cdot (4\mu_3^2\, p(1 - p))^{L/2}$; for $T$ at most polynomial in $L$ this falls exponentially in
$L$. The bound is in fact for the larger event that $E + E'$ contains a self-avoiding closed path that is homologically
nontrivial in the spatial directions; such a path alone is not a failure, since two parallel winding paths together
bound a strip. With the estimate $\mu_3 \approx 4.684$ that Dennis, Kitaev, Landahl and Preskill quote, the conditions
hold for $p, q < 0.0114$, slightly below the root $\approx 0.01153$ at $\mu_3 = 4.684$; that decimal is an estimate, not
a certified bound (a certified bound $\mu_3 < 4.7098$ would suffice). A decoder that
sees a finite record without the final error-free round needs its own rule at the last round, where a single wrong
readout leaves an unpaired detection event; this page does not cover it.

## Expansion

The proof uses the weighted bound for a fixed self-avoiding closed spacetime path contained in $E + E'$ (linked below). A
good expansion adds the spacetime versions of the remaining two steps of the
[perfect-syndrome threshold](threshold-for-minimum-weight-decoding-of-the-toric-code.md): a failure, a nonzero total spatial homology class of
$E + E'$, needs a self-avoiding closed path in the spacetime slab of length at least $L$ that is homologically
nontrivial in the spatial directions; and the count of
self-avoiding walks from a fixed vertex of the cubic lattice, at most $\mu_3^{\ell} e^{o(\ell)}$, with the $L^2 (T + 1)$
vertices of the slab as starting points. Dennis, Kitaev, Landahl and Preskill state the argument for the complete
history, counting walks between two time slices; the expansion checks that it applies unchanged in the finite slab.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Proof depends on

- [The probability that a fixed cycle lies in the error plus the correction](probability-that-a-fixed-cycle-lies-in-the-error-plus-the-correction.md): the weighted bound for a fixed self-avoiding closed spacetime path contained in $E + E'$ on the finite record.

## Related topics

- [Threshold for minimum-weight decoding of the toric code](threshold-for-minimum-weight-decoding-of-the-toric-code.md): the case of perfect syndrome measurements.

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.A, equations (44)–(46) (the weights), Section V.B, equations (47)–(55) (the weighted bound on a fixed path and the failure bound), Section V.C, equations (58)–(64) (the cubic-lattice count; the constant (58) and the decimals (63)–(64) are approximate, and the bound is stated there with a polynomial factor from a count of closed polygons), Section IV.C (the syndrome chain and its boundary), and the opening of Section VI (the complete syndrome history assumed in Section V, replaced here by a finite record with an error-free final round).
