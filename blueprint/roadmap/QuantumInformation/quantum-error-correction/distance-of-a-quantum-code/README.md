# Distance of a quantum code

The $n$-qubit Pauli operators $X^a Z^b$ ($a, b \in \mathbb{F}_2^n$) form a basis of the operators on $n$ qubits, and products of Pauli operators are Pauli operators up to a sign. The weight of $X^a Z^b$ is the number of qubits on which it acts nontrivially. A code has distance $d$ when every Pauli operator $E$ of weight less than $d$ satisfies $\langle \bar\imath | E | \bar\jmath \rangle = c_E \delta_{ij}$ on an orthonormal basis of the code, and some operator of weight $d$ does not (Preskill, equation (7.34)); it is then an $[[n, k, d]]$ code. Since $E_a^{*} E_b$ has weight at most $2t$ when $E_a$ and $E_b$ have weight at most $t$, the Knill–Laflamme conditions show that a code of distance $2t + 1$ corrects $t$ errors (Preskill, Section 7.3.1).

Here "distance at least $d$" is defined with the Pauli operators of [CSS codes](../css-codes/README.md), and the correction of $t$ errors follows from the sufficiency of the Knill–Laflamme conditions. The quantum Singleton bound $n - k \ge 2(d - 1)$ (Preskill, equation (7.103)) bounds the parameters of such codes.

- [Weight of a Pauli operator](pauli-weight.md)
- [Pauli weight as a Hamming norm](pauli-weight-eq-hamming-norm.md)
- [Product of two Pauli operators](conj-transpose-pauli-mul-pauli.md)
- [Weight of a product of Pauli operators](pauli-weight-add-le.md)
- [Distance of a quantum code (lower bound)](has-distance-at-least.md)
- [A code of distance $2t + 1$ corrects $t$ errors](is-correctable-of-has-distance-at-least.md)
- [The quantum Singleton bound](quantum-singleton-bound.md)

## Related topics

- [Knill–Laflamme conditions](../knill-laflamme-conditions/README.md): the criterion from which the correction of $t$ errors follows.
- [Bounds on code size](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/README.md): the classical counterpart, where a minimum distance $2t + 1$ likewise allows correcting $t$ errors.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Sections 7.2, 7.3.1 and 7.9.1.
