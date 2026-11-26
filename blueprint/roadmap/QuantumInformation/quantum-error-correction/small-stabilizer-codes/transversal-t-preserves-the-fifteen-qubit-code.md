# Transversal $T$ preserves the fifteen-qubit code

Let $T = \operatorname{diag}(1, e^{i\pi/4})$. The transversal operator $T^{\otimes 15}$ maps the code space of the
[fifteen-qubit code](fifteen-qubit-quantum-reed-muller-code.md) onto itself. Since $T$ is not a Clifford gate, the
code admits a transversal gate outside the Clifford group; this is what makes it useful for distilling magic states.

Proof (Bravyi and Kitaev): conjugation by $T$ fixes $Z$ and maps $X$ to $A = \tfrac{1}{\sqrt 2}(X + Y)$, so
$T^{\otimes 15}$ maps the code onto the joint $+1$ eigenspace of the operators $Z^v$ ($v \in L_2$) and
$A^{\otimes u}$ ($u \in L_1$, the tensor product of $A$ over the support of $u$). Bravyi and Kitaev show that this
eigenspace is the code itself (their Lemma 2), using that $|u| \equiv 0 \pmod 8$ for $u \in L_1$ and that the
componentwise product of $u \in L_1$ and $v \in L_2^{\perp}$ has weight divisible by $4$ (their Lemma 1).

## Depends on

- [The fifteen-qubit quantum Reed–Muller code](fifteen-qubit-quantum-reed-muller-code.md)
- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)
- [Transversal gate](../fault-tolerant-gates/transversal-gate.md)

## Proof depends on

- [Conjugation of Pauli operators by $H$, $S$ and CNOT](../clifford-group/conjugation-of-pauli-operators-by-h-s-and-cnot.md)
- [The $T$ gate is in the third level of the Clifford hierarchy](../clifford-group/t-gate-is-in-the-third-level-of-the-clifford-hierarchy.md)

## Sources

- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section VI, Lemma 1 and the paragraph after Lemma 2 ("the bitwise application of $W$ i.e., the operator $W^{\otimes 15}$ preserves the code subspace").
