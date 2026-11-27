# Farkas certificates for linear rational arithmetic

Let $A \in \mathbb{Q}^{m \times n}$ and $b \in \mathbb{Q}^m$. The system $Ax \le b$ has no rational solution if and only if there is $y \in \mathbb{Q}^m$ with $y \ge 0$, $y^{\mathsf T} A = 0$ and $y^{\mathsf T} b < 0$. Such a $y$ is a certificate of infeasibility that can be checked by linear algebra; its existence for every infeasible system follows by induction on $n$ using Fourier–Motzkin elimination.

## Proof depends on

- [Fourier–Motzkin elimination](fouriermotzkin-elimination.md)
- [Farkas' lemma over linearly ordered fields](../../../LinearAlgebra/matrix-algebra/linear-inequality-systems-over-ordered-fields/farkas-lemma-over-ordered-fields.md)

## Sources

- A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986
- M. Lavrov, "Lecture 20: Fourier–Motzkin elimination", Math 482 lecture notes, University of Illinois, 2020, Section 3 and Theorem 3.1, <https://misha.fish/archive/docs/482-spring-2020/lecture20.pdf>
- D. Kroening and O. Strichman, *Decision Procedures: An Algorithmic Point of View*, 2nd ed., Springer, 2016
