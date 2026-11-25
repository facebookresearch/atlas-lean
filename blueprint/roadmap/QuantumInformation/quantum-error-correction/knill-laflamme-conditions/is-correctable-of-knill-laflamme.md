# Sufficiency of the Knill–Laflamme conditions

Let $P$ be an orthogonal projector ($P^{*} = P$, $P^2 = P$) on a finite-dimensional complex
Hilbert space and let $(A_a)_{a \in \iota}$ be error operators, indexed by an arbitrary type. If
for all $a$ and $b$ there is a scalar $c_{ab}$ with $P A_a^{*} A_b P = c_{ab} P$, then the errors
are [correctable](is-correctable.md) on the code $\operatorname{range} P$: one recovery channel
with finitely many Kraus operators restores every code state after every error, up to a scalar.
This is the "if" half of Knill and Laflamme's Theorem 3.2, stated with the projector $P$ in place
of an orthonormal basis of the code. The family of errors may be infinite, which the source also
allows (it remarks after the definition of $\mathcal{A}$-correcting codes that $\mathcal{A}$ need
not be finite).

The proof follows the construction in Preskill's notes. If $P = 0$ any channel works. Otherwise
let $W$ be the span of the operators $A_a P$. On $W$ the Hilbert–Schmidt inner product
$\langle X, Y \rangle = \operatorname{tr}(X^{*} Y)$ is tied to the conditions: for $X, Y \in W$
one has $X = XP$ and $P X^{*} Y P = \frac{\operatorname{tr}(X^{*} Y)}{\operatorname{tr} P} P$.
Choose an orthonormal basis of $W$ and rescale it by $\sqrt{\operatorname{tr} P}$ to get operators
$F_1, \dots, F_m$ with $F_i^{*} F_j = \delta_{ij} P$; this is the diagonalisation of the matrix
$C$ in Preskill's equation (7.28). The recovery has Kraus operators $R_i = P F_i^{*}$ (equation
(7.29)) and $R_0 = I - Q$, where $Q = \sum_i F_i F_i^{*}$ is the projector onto the span of the
corrupted code spaces (equation (7.32)). Then $\sum_r R_r^{*} R_r = Q + (I - Q) = I$, each
$R_i A_a P$ is the $i$-th coefficient of $A_a P$ in the $F_j$ times $P$, and $R_0 A_a P = 0$.
These Kraus operators, built from the $F_i$, are the recovery channel required by the definition
of correctability.

The hypotheses are satisfiable by nontrivial codes: on two qubits, the code spanned by
$|00\rangle$ and $|11\rangle$ satisfies them for the errors $\{I, X \otimes I\}$, which are therefore
correctable.

## Sources

- E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55 (1997), 900–911, arXiv:quant-ph/9604034, Section 3.1 and Theorems 3.1–3.2.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2, equations (7.19)–(7.32).
