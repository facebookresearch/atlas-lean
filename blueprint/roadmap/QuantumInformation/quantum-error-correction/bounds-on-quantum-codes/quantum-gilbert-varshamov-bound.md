# The quantum Gilbert–Varshamov bound

Let $n, k \ge 1$ and $d \ge 1$. If

$$\sum_{j=0}^{d-1} 3^j \binom{n}{j} \cdot 2^k \;\le\; 2^n ,$$

then there is a subspace of $n$ qubits of dimension $2^k$ with
[distance at least $d$](../distance-of-a-quantum-code/has-distance-at-least.md), that is, an $[[n, k, d']]$ code with
$d' \ge d$. The sum counts the Pauli operators of weight less than $d$, whose matrix elements on the code the
Knill–Laflamme conditions constrain. Compared with the [quantum Hamming bound](quantum-hamming-bound.md) for $t$ errors the sum runs to
$d - 1$ instead of $t$; for odd $d = 2t + 1$ that is $2t$. Asymptotically, for $0 < p$ with
$R(p) = 1 - H_2(2p) - 2p \log_2 3 > 0$, where $H_2$ is the binary entropy, every rate below $R(p)$ is achievable: for all
large $n$ there are codes with $d \ge 2pn$ and $k/n$ at least that rate. Outside this range the bound gives nothing; for
instance $d = n$ with $k \ge 1$ is impossible for large $n$ by the quantum Singleton bound.

## Expansion

A good expansion adds a checked proof. Gottesman's thesis (Section 7.1) builds the code greedily: choose codewords one
at a time, each orthogonal to the images of the earlier ones under all operators of weight less than $d$ and satisfying
generic constraints on the diagonal matrix elements; the genericity step needs a precise statement, and the
author's errata to Section 7.1 say that this proof is incomplete and point to a complete one. Preskill
(Section 7.14) sketches the counting argument over stabilizer groups for the asymptotic form, which needs its exact
counts stated. The page then depends on that construction and on the
[Knill–Laflamme conditions](../knill-laflamme-conditions/is-correctable-iff-knill-laflamme.md).

## Depends on

- [Distance of a quantum code (lower bound)](../distance-of-a-quantum-code/has-distance-at-least.md)
- [Weight of a Pauli operator](../distance-of-a-quantum-code/pauli-weight.md)

## Informally uses

- [The Knill–Laflamme conditions](../knill-laflamme-conditions/is-correctable-iff-knill-laflamme.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2, equations (36)–(37) and Theorem 4 (the finite sufficient condition (36)).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 7.1, equations (7.4)–(7.9).
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.14, equations (7.198)–(7.200).
