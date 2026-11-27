# Auxiliary-input one-way functions

An **auxiliary-input one-way function** secure against a class $\mathcal{C}$ of adversaries (Hirahara–Nanashima, Definition 4.6) is a polynomial-time computable family $f=\{f_z\}_{z\in\{0,1\}^*}$ with $f_z:\{0,1\}^{p(|z|)}\to\{0,1\}^*$ such that for every adversary $A \in \mathcal{C}$ (e.g., probabilistic polynomial-time algorithms, $\mathsf{P/poly}$, or $\mathrm{SIZE}[2^{\epsilon n}]$) and every sufficiently large $n \in \mathbb{N}$, there exists an auxiliary input $z = z_{n,A} \in \{0,1\}^n$ for which

$$
\Pr_{x\sim\{0,1\}^{p(n)}}\bigl[f_z(A(z,f_z(x)))=f_z(x)\bigr]<\mathrm{negl}(n).
$$

(An *infinitely-often* variant asks only for infinitely many hard auxiliary inputs $z$ per adversary $A$, as in Ostrovsky–Wigderson's original formulation, which is strictly weaker than the almost-everywhere-in-length Definition 4.6 used by Hirahara–Nanashima.) The order of quantifiers is weaker than for a standard one-way function because the hard index $z$ may depend on the adversary. Ostrovsky and Wigderson showed that worst-case hardness of computational zero knowledge ($\mathsf{CZK}\not\subseteq\mathsf{BPP}$) implies the existence of infinitely-often auxiliary-input one-way functions.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Sources

- Shuichi Hirahara and Mikito Nanashima, "One-Way Functions and Zero Knowledge", STOC (2024), ECCC TR24-063 (Definition 4.6).
- Rafail Ostrovsky and Avi Wigderson, "One-Way Functions Are Essential for Non-Trivial Zero-Knowledge", ISTCS (1993).
