# Qudit Pauli operators over a finite field

Let $q = p^m$ be a prime power, $\mathbb{F}_q$ the field with $q$ elements, $\operatorname{tr} : \mathbb{F}_q \to \mathbb{F}_p$
the field trace and $\omega = e^{2\pi i / p}$. On $\mathbb{C}^q$ with basis $|x\rangle$, $x \in \mathbb{F}_q$, define

$$X(a) |x\rangle = |x + a\rangle, \qquad Z(b) |x\rangle = \omega^{\operatorname{tr}(b x)} |x\rangle \qquad (a, b \in \mathbb{F}_q),$$

and on $(\mathbb{C}^q)^{\otimes n}$ let $X(\mathbf a) Z(\mathbf b) = X(a_1) Z(b_1) \otimes \cdots \otimes X(a_n) Z(b_n)$ for
$\mathbf a, \mathbf b \in \mathbb{F}_q^n$. These $q^{2n}$ operators form a *nice error basis*: they contain $I$, a product
of two of them is a scalar multiple of a third, and $\operatorname{Tr}(A^{*} B) = 0$ for distinct $A, B$, so they are a
basis of the $q^n \times q^n$ matrices. The error group $G_n$ consists of the $\omega^c X(\mathbf a) Z(\mathbf b)$, and
two of its elements commute exactly when the trace-symplectic form
$\operatorname{tr}(\mathbf b \cdot \mathbf a' - \mathbf b' \cdot \mathbf a)$ vanishes. For $q = 2$ these are the qubit
Pauli operators $X^a Z^b$ up to phase. When $p = 2$ the phases $\omega^c = \pm 1$ do not suffice to build stabilizers: for
$n = 1$ and $q = 2$ the vector $(1, 1)$ lifts only to $\pm XZ$, which square to $-I$. Stabilizer codes in characteristic
$2$ therefore use the extension $\tilde G_n$ of $G_n$ by the phases $i^c$, which contains $iXZ = Y$; this extension is a
convention of this page, not part of Ketkar et al.'s definition of $G_n$.

## Depends on

- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)

## Sources

- A. Ketkar, A. Klappenecker, S. Kumar and P. K. Sarvepalli, *Nonbinary stabilizer codes over finite fields*, IEEE Trans. Inform. Theory 52 (2006), 4892–4914, arXiv:quant-ph/0508070, Section II, the definitions of $X(a)$ and $Z(b)$, Lemma 1, Corollary 4 and Lemma 5.
