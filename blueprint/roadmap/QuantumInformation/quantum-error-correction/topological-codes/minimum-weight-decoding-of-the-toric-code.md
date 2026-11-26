# Minimum-weight decoding of the toric code

Consider bit-flip errors on the [toric code](toric-code.md): an error $X^e$ for a set $e$ of edges. Its syndrome is the
set $D$ of faces $p$ with $B_p X^e = -X^e B_p$, the faces containing an odd number of edges of $e$ (the endpoints of the
dual chain of $e$, the defects). Given $D$, the minimum-weight decoder chooses a set $e'$ of edges of least size whose
set of odd faces is $D$, and applies $X^{e'}$; when several sets are minimal, one is chosen. Equivalently it pairs the
defects by a minimum-weight perfect matching, the weight of a pair being their distance on the dual lattice, and joins
each pair by a shortest dual path. Recovery succeeds when $e + e'$ is the coboundary of a set of vertices, so that
$X^{e + e'}$ lies in the stabilizer, and fails when $e + e'$ winds around the torus. Phase-flip errors are decoded in the
same way using the vertex operators. With independent errors of different rates, for instance with faulty syndrome
measurements, the decoder minimises a weighted length instead.

## Depends on

- [Toric code](toric-code.md)
- [Error syndrome of a stabilizer code](../stabilizer-formalism/error-syndrome.md)

## Background

- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.A, equation (46).
