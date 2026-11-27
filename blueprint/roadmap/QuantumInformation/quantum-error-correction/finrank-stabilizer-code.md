# Dimension of a stabilizer code

Let $M_j = c_j X^{a_j} Z^{b_j}$ ($j = 1, \dots, r$) be scalar multiples of Pauli operators on $n$
qubits ([Pauli operators](css-codes/pauli.md) $X^a Z^b$, $a, b \in \mathbb{F}_2^n$) such that
- $M_j^2 = I$ for every $j$,
- $M_j M_k = M_k M_j$ for all $j, k$,
- the vectors $(a_j, b_j) \in \mathbb{F}_2^n \times \mathbb{F}_2^n$ are linearly independent over
  $\mathbb{F}_2$.

Then the stabilizer code $\{\psi : M_j \psi = \psi \text{ for all } j\}$ has dimension
$2^{n - r}$. This is the count in Preskill's Section 7.9.1 ("If $S$ has $n - k$ generators, we can
show that the code space $H_S$ has dimension $2^k$") and in Gottesman's thesis, Section 3.2
("provided it is Abelian and neither $i$ nor $-1$ is in $S$, the space $T$ … does have dimension
$2^k$", for $|S| = 2^{n-k}$).

The $M_j$ generate the abelian group $S = \{\prod_{j \in J} M_j\}$. Linear independence of the
$(a_j, b_j)$ says that no generator is a product of the others and that no nonempty product of
generators is a scalar multiple of $I$; in particular $-I \notin S$, the condition in the sources.
Pairwise commutation makes the span of the $(a_j, b_j)$ isotropic for the symplectic form, which
forces $r \le n$, so $2^{n - r}$ involves no truncated subtraction. Preskill's proof halves the
dimension one generator at a time, using an element of the Pauli group that commutes with
$M_1, \dots, M_{j-1}$ and anticommutes with $M_j$.

The hypotheses are jointly satisfiable: the single generator $Z$ on one qubit ($r = 1$) squares to
$I$ and has the nonzero vector $(0, 1)$; commutation of a single generator with itself is automatic.
Its code is spanned by $|0\rangle$, of dimension $2^0$.

## Background

- [Product of two Pauli operators](distance-of-a-quantum-code/conj-transpose-pauli-mul-pauli.md): products of the generators are again Pauli operators up to a sign, so $S$ consists of $2^r$ such operators.
- [CSS codes](css-codes/README.md): CSS codes are the stabilizer codes whose generators are all of the form $X^a$ or $Z^b$.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.1, equations (7.117)–(7.120).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.2.
