# The quantum Singleton bound

Let $P$ be the orthogonal projector onto a code of dimension $2^k$, with $k \ge 1$, in the space
of $n$ qubits, and suppose the code has [distance at least $d$](has-distance-at-least.md). Then

$$n - k \ge 2(d - 1),$$

stated as $k + 2(d - 1) \le n$ to avoid truncated subtraction. This is Preskill's equation
(7.103). It resembles the classical Singleton bound $n - k \ge d - 1$, with twice the
redundancy, and the $[[5, 1, 3]]$ code attains it.

Preskill's proof: maximally entangle the code with a $k$-qubit reference system $A$, so that
$S(A) = k$. Split the $n$ qubits into two blocks $Q^{(1)}, Q^{(2)}$ of $d - 1$ qubits and the rest
$Q^{(3)}$. Because the code has distance $d$, no observable on $d - 1$ qubits reveals anything
about the encoded state, so $A Q^{(1)}$ and $A Q^{(2)}$ are uncorrelated: $S(A Q^{(i)}) =
S(A) + S(Q^{(i)})$. Purity of the global state and subadditivity of the von Neumann entropy then
give $S(A) \le S(Q^{(3)}) \le n - 2(d - 1)$.

The hypothesis $k \ge 1$ is needed: a one-dimensional code ($k = 0$) has distance at least $d$
for every $d$. The hypotheses are jointly satisfiable, for instance by the whole space of two
qubits ($P = I$, $k = 2$, $d = 1$).

## Background

- [Bounds on code size](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/README.md): the classical Singleton bound that this statement parallels.
- [No-cloning theorem (linear form)](../../quantum-operations/no-cloning-linear.md): Preskill first derives the weaker bound $n > 2(d - 1)$ (equation (7.102), Section 7.8.2) from the impossibility of cloning, by splitting a block with $d - 1$ located errors into two offspring.
- [Subadditivity of entropy](../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/shannon-entropy-le-add.md): the classical (Shannon) form of the subadditivity that the proof uses for the von Neumann entropy.
- [Lieb's concavity theorem](../../../LinearAlgebra/positive-definite-matrices/lieb-s-concavity-theorem/README.md): it implies strong subadditivity of the von Neumann entropy.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Sections 7.8.2–7.8.3, equations (7.102)–(7.112).
