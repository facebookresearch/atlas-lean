# Minimum-weight decoding fails only on a homologically nontrivial cycle

In the setting of [minimum-weight decoding](minimum-weight-decoding-of-the-toric-code.md) of bit flips on the
$L \times L$ [toric code](toric-code.md), the edge set $E + E_{\min}$ has empty boundary, so it is a cycle and decomposes
into edge-disjoint self-avoiding closed paths. Decoding succeeds (the correction returns the encoded state) exactly when
$E + E_{\min}$ is homologically trivial, since a trivial cycle is a product of face operators, which act as the identity
on the code, while a nontrivial cycle is a logical operator. Hence decoding fails only if $E + E_{\min}$ contains a
homologically nontrivial self-avoiding closed path, which has [at least $L$ edges](homologically-nontrivial-cycles-on-the-torus-have-length-at-least-l.md).
Summing the [bound for a fixed path](probability-that-a-fixed-cycle-lies-in-the-error-plus-the-correction.md) over the
paths of each length $\ell \ge L$ bounds the failure probability. Such a path lifts to a self-avoiding walk on
$\mathbb{Z}^2$, not to a closed polygon, so there are at most $L^2 c_\ell$ of them, with $c_\ell$ the number of
[self-avoiding walks](counting-self-avoiding-walks-on-the-square-lattice.md) of length $\ell$ from a fixed vertex
(Dennis, Kitaev, Landahl and Preskill count closed polygons here).

## Depends on

- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Proof depends on

- [Homologically nontrivial cycles on the $L \times L$ torus have length at least $L$](homologically-nontrivial-cycles-on-the-torus-have-length-at-least-l.md)
- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.B, the paragraph before equation (55) and equation (55); the count of polygons there is replaced by a count of walks.
