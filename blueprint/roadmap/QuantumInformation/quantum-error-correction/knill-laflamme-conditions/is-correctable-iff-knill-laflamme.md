# The Knill–Laflamme conditions

Let $P$ be an orthogonal projector ($P^{*} = P$, $P^2 = P$) on a finite-dimensional complex
Hilbert space. A family of error operators $A_a$ is [correctable](is-correctable.md) on the code
$\operatorname{range} P$ if and only if for all $a$ and $b$ there is a scalar $c_{ab}$ with

$$P A_a^{*} A_b P = c_{ab} P.$$

This is Knill and Laflamme's Theorem 3.2 in projector form, and Preskill's criterion (7.19)
$\langle \bar\jmath | E_b^{\dagger} E_a | \bar\imath \rangle = C_{ba} \delta_{ij}$ for an
orthonormal basis $|\bar\imath\rangle$ of the code. When $P \neq 0$ the matrix $(c_{ab})$ is then
automatically Hermitian and positive semidefinite; when $P = 0$ every matrix works, the zero matrix
among them.

It combines the [necessity](knill-laflamme-of-is-correctable.md) and the
[sufficiency](is-correctable-of-knill-laflamme.md) halves. The conditions are sesquilinear in the errors, so they hold for a family exactly when they
hold for its linear span, in line with the fact that
[correctable errors form a linear space](is-correctable-of-forall-mem-span.md): a code that
corrects the Pauli errors on $t$ qubits corrects every error on those qubits (Preskill,
Section 7.2).

## Informally uses

- [Necessity of the Knill–Laflamme conditions](knill-laflamme-of-is-correctable.md): the
  "only if" direction.
- [Sufficiency of the Knill–Laflamme conditions](is-correctable-of-knill-laflamme.md): the
  "if" direction.

## Sources

- E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55 (1997), 900–911, arXiv:quant-ph/9604034, Section 3.1 and Theorems 3.1–3.2.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2, equations (7.19)–(7.32).
