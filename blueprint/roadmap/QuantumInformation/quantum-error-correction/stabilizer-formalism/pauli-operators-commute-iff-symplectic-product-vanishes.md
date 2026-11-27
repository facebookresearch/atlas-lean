# Pauli operators commute exactly when their symplectic product vanishes

For all $a, b, a', b' \in \mathbb{F}_2^n$,

$$(X^a Z^b)(X^{a'} Z^{b'}) = (-1)^{\omega((a, b), (a', b'))}\, (X^{a'} Z^{b'})(X^a Z^b),$$

where $\omega$ is the [symplectic product](symplectic-product-of-pauli-operators.md). Hence two Pauli operators
commute when $\omega = 0$ and anticommute when $\omega = 1$; since phases are central, any two elements of the
$n$-qubit Pauli group either commute or anticommute.

Proof: on a basis state, $X^a Z^b X^{a'} Z^{b'} |v\rangle = (-1)^{b' \cdot v + b \cdot (v + a')} |v + a + a'\rangle$ and
$X^{a'} Z^{b'} X^a Z^b |v\rangle = (-1)^{b \cdot v + b' \cdot (v + a)} |v + a + a'\rangle$; the ratio of the two signs is
$(-1)^{a' \cdot b + a \cdot b'}$.

## Depends on

- [Pauli operator $X^a Z^b$ on $n$ qubits](../css-codes/pauli.md)
- [Symplectic product of Pauli operators](symplectic-product-of-pauli-operators.md)

## Proof depends on

- [Action of a Pauli operator on a vector](../css-codes/pauli-mul-vec-apply.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.1, property (iv), and Section 7.9.2, equation (7.129).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.4, equation (3.23).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 3.1, the paragraph before equation (56).
