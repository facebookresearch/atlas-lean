# Minimum-weight decoding fails only on a homologically nontrivial cycle

In the setting of [minimum-weight decoding](minimum-weight-decoding-of-the-toric-code.md) of bit flips on the
$L \times L$ [toric code](toric-code.md), the edge set $E + E_{\min}$ has empty boundary on the dual lattice (every face
meets it in an even number of edges), so it is a cycle of the dual lattice and decomposes into edge-disjoint
self-avoiding closed dual paths. Decoding succeeds (the correction returns the encoded state) exactly when the total
homology class of $E + E_{\min}$ is zero: a trivial dual cycle is the coboundary of a set of vertices, so $X^{E + E_{\min}}$
is a product of vertex operators $A_s$, which act as the identity on the code, while a dual cycle with nonzero class is a
logical operator. (For phase flips the roles are exchanged: a trivial cycle of the primal lattice is a product of face
operators.) Hence decoding fails only if $E + E_{\min}$ contains a homologically nontrivial self-avoiding closed dual
path, which has [at least $L$ edges](homologically-nontrivial-cycles-on-the-torus-have-length-at-least-l.md); the
[threshold](threshold-for-minimum-weight-decoding-of-the-toric-code.md) bounds the probability of that larger event.

## Depends on

- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Proof depends on

- [Homologically nontrivial cycles on the $L \times L$ torus have length at least $L$](homologically-nontrivial-cycles-on-the-torus-have-length-at-least-l.md)
- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)

## Related topics

- [Threshold for minimum-weight decoding of the toric code](threshold-for-minimum-weight-decoding-of-the-toric-code.md): bounds the probability of the larger event by counting paths.

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section III.A (vertex and face operators, and the dual lattice for bit flips) and Section V.B (success as homology of the estimated and actual chains, and the paragraph before equation (55)).
