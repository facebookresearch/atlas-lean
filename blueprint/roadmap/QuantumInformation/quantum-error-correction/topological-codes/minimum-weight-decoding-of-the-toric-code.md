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
instead record the syndrome history over $T$ rounds and match the changes of the syndrome in a three-dimensional
spacetime lattice, with space-like edges for data errors of rate $p$ and time-like edges for readout errors of rate $q$,
weighted by $\log((1 - p)/p)$ and $\log((1 - q)/q)$.

## Depends on

- [Toric code](toric-code.md)
- [Error syndrome of a stabilizer code](../stabilizer-formalism/error-syndrome.md)
- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section IV, equations (44)–(46) (the syndrome history and the weights), and Section V.A.
