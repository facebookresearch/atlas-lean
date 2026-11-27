# Stabilizer formalism

A stabilizer code is the joint $+1$ eigenspace of an abelian group $S$ of Pauli operators with $-I \notin S$. Modulo phases,
Pauli operators are vectors of $\mathbb{F}_2^{2n}$, and two of them commute exactly when their symplectic product vanishes;
the normalizer of $S$, the operators that preserve the code, is then the symplectic complement of $S$. Measuring the
generators yields the error syndrome, which identifies errors up to the normalizer, and the normalizer modulo $S$ is the
group of logical Pauli operators on the $k$ encoded qubits. Generators can be put in a standard form from which an
encoding circuit is read off, and stabilizer codes correspond to self-orthogonal additive codes over $\mathrm{GF}(4)$
(Gottesman's thesis, Chapters 3–4; Preskill, Section 7.9). The correctability criterion, the dimension formula and the
definitions of the Pauli and Clifford groups are on the pages linked under related topics.

- [Every matrix is a combination of Pauli operators](pauli-expansion-of-a-matrix.md)
- [Symplectic product of Pauli operators](symplectic-product-of-pauli-operators.md)
- [Pauli operators commute exactly when their symplectic product vanishes](pauli-operators-commute-iff-symplectic-product-vanishes.md)
- [The normalizer of a stabilizer group is its centralizer](normalizer-of-a-stabilizer-group-equals-its-centralizer.md)
- [Order of the normalizer of a stabilizer group](order-of-the-normalizer-of-a-stabilizer-group.md)
- [Error syndrome of a stabilizer code](error-syndrome.md)
- [The syndrome map is a homomorphism with kernel the normalizer](syndrome-map-is-a-homomorphism-with-kernel-the-normalizer.md)
- [Every syndrome is the syndrome of a Pauli operator](every-syndrome-is-the-syndrome-of-a-pauli-operator.md)
- [Logical Pauli operators of a stabilizer code](logical-pauli-operators-of-a-stabilizer-code.md)
- [Standard form of a stabilizer code](standard-form-of-a-stabilizer-code.md)
- [Encoding circuit for a stabilizer code](encoding-circuit-for-a-stabilizer-code.md)
- [Stabilizer codes from additive codes over GF(4)](stabilizer-codes-from-additive-codes-over-gf4.md)
- [The number of stabilizer states](number-of-stabilizer-states.md)
- [Pauli operators are orthogonal for the trace inner product](pauli-operators-form-an-orthogonal-basis.md)
- [Symplectic Gram–Schmidt over $\mathbb{F}_2$](symplectic-gram-schmidt-over-f2.md)
- [Graph state](graph-state.md)
- [Every stabilizer state is local-Clifford equivalent to a graph state](every-stabilizer-state-is-local-clifford-equivalent-to-a-graph-state.md)
- [Qudit Pauli operators over a finite field](qudit-pauli-operators-over-a-finite-field.md)
- [Qudit stabilizer codes correspond to symplectic self-orthogonal additive codes](qudit-stabilizer-codes-from-symplectic-self-orthogonal-codes.md)

## Related topics

- [Dimension of a stabilizer code](../stabilizer-codes/finrank-stabilizer-code.md): the dimension $2^{n-r}$ of a stabilizer code with $r$ independent generators.
- [Stabilizer codes: correctability criterion and distance](../stabilizer-codes-correctability-criterion-and-distance.md): correctability and distance in terms of the normalizer.
- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md): the Pauli group and its binary representation.
- [The Clifford group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/clifford-group-on-n-qubits.md): the Clifford group and the projective Clifford group

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Sections 2.3, 3.1 and 3.4.
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Chapters 3–4.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.
