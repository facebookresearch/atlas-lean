# Minimum-weight decoding of the toric code

Consider bit-flip errors on the [toric code](toric-code.md): an error $X^e$ for a set $e$ of edges. Its syndrome is the
set $D$ of faces $p$ with $B_p X^e = -X^e B_p$, the faces containing an odd number of edges of $e$ (the endpoints of the
dual chain of $e$, the defects). Given $D$, the minimum-weight decoder chooses a set $e'$ of edges of least size whose
set of odd faces is $D$, and applies $X^{e'}$; when several sets are minimal, one is chosen. Equivalently it pairs the
defects by a minimum-weight perfect matching, the weight of a pair being their distance on the dual lattice, and joins
each pair by a shortest dual path. Recovery succeeds when $e + e'$ is homologically trivial (the boundary of a set of faces), so that
$X^{e + e'}$ lies in the stabilizer, and fails when its total homology class is nonzero; two parallel winding loops
together bound a strip and do not cause failure. Phase-flip errors are decoded in the
same way using the vertex operators. When syndrome measurements are themselves faulty, a spatial matching of one round's defects
no longer works, since a single wrong readout produces an isolated apparent defect. Dennis, Kitaev, Landahl and Preskill
then work in a three-dimensional spacetime lattice: space-like edges stand for data errors of rate $p$ in a round,
time-like edges for readout errors of rate $q$, and the syndrome chain $S$ records where the measured syndrome changes.
Their analysis assumes the complete syndrome history, with measurements repeated indefinitely, so that $S + E$ is a
cycle (the closed world lines of the defects) for the error chain $E$. The decoder chooses a chain $E'$ with
$\partial E' = \partial S$ of least weighted length $H \log((1 - p)/p) + V \log((1 - q)/q)$, for $H$ space-like and $V$
time-like edges and $0 < p, q < 1/2$; when $p = 0$ or $q = 0$ the edges of that type are not used. Decoding fails when
$E + E'$ contains a cycle that is homologically nontrivial in the spatial directions. A decoder that sees only a finite
record of rounds needs a rule at the last round, where a single wrong readout leaves an unpaired change; Dennis, Kitaev,
Landahl and Preskill treat that case separately, with chains closed relative to the final time slice.

## Depends on

- [Toric code](toric-code.md)
- [Error syndrome of a stabilizer code](../stabilizer-formalism/error-syndrome.md)
- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.A, equations (44)–(46) (the weights and the minimal chain), Section V.B (failure as a homologically nontrivial path in $E + E_{\min}$), and the opening of Section VI (the complete syndrome history assumed in Section V) and Section VI.A (a finite record, with chains closed relative to the final time slice).
