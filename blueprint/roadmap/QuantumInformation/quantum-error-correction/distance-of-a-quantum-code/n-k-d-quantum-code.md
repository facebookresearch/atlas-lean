# $[[n, k, d]]$ quantum code

Let $n \ge 1$, $k \ge 1$ and $d \ge 1$. An $[[n, k, d]]$ quantum code is a subspace $Q$ of the space
$(\mathbb{C}^2)^{\otimes n}$ of $n$ qubits with $\dim Q = 2^k$ whose orthogonal projector $P$ has
[distance at least $d$](has-distance-at-least.md) and not distance at least $d + 1$: every Pauli operator $X^a Z^b$
of [weight](pauli-weight.md) less than $d$ satisfies $P X^a Z^b P = c_{a,b} P$ for a scalar $c_{a,b}$, and some Pauli
operator of weight $d$ does not. So $d$ is Preskill's distance, the minimum weight of a Pauli operator $E$ with
$\langle \bar\imath | E | \bar\jmath \rangle \ne C_E \delta_{ij}$, and $k$ is the number of encoded qubits.

For $k \ge 1$ such a $d$ exists and $d \le n$ by the [quantum Singleton bound](quantum-singleton-bound.md). The double
brackets distinguish quantum from classical $[n, k, d]$ codes. Gottesman and Calderbank, Rains, Shor and Sloane also
admit $k = 0$ by a separate convention (a single state, required to be nondegenerate), which is not covered here.

## Depends on

- [Distance of a quantum code (lower bound)](has-distance-at-least.md)
- [Weight of a Pauli operator](pauli-weight.md)

## Proof depends on

- [The quantum Singleton bound](quantum-singleton-bound.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.3.1, equation (7.34).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 2.3 and Section 3.2 (the convention for $[n, 0, d]$ codes).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.2.
