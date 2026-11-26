# Auxiliary-input one-way functions

An **auxiliary-input one-way function** is a polynomial-time computable family $f=\{f_z\}_{z\in\{0,1\}^*}$ with $f_z:\{0,1\}^{p(|z|)}\to\{0,1\}^*$ such that for every probabilistic polynomial-time algorithm $A$ and every polynomial $q$ there are infinitely many auxiliary inputs $z$ for which

$$
\Pr_{x\sim\{0,1\}^{p(|z|)}}\bigl[f_z(A(z,f_z(x)))=f_z(x)\bigr]<\frac{1}{q(|z|)}.
$$

The order of quantifiers is weaker than for a standard one-way function: the hard index $z$ may depend on the adversary. Security against $\mathsf{P/poly}$ or against $\mathrm{SIZE}[2^{\epsilon n}]$ is defined with non-uniform adversaries. Ostrovsky and Wigderson showed that worst-case hardness of computational zero knowledge ($\mathsf{CZK}\not\subseteq\mathsf{BPP}$) implies the existence of auxiliary-input one-way functions.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Sources

- Shuichi Hirahara and Mikito Nanashima, "One-Way Functions and Zero Knowledge", STOC (2024), ECCC TR24-063.
