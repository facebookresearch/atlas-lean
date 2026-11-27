# The Diophantine problem in a free associative algebra over any field is undecidable

For every field $K$ and every nonempty set $A$, no algorithm decides whether a polynomial equation with coefficients in the free associative algebra over the prime subfield of $K$ has a solution in the free associative algebra $K\langle A\rangle$.

**Setting (Kharlampovich and Myasnikov).** Let $K$ be a field, $A$ a nonempty set and $K\langle A\rangle$ the free associative unital $K$-algebra with basis $A$, the noncommutative polynomials in the letters of $A$. An *equation* in variables $X = \{x_1, \dots, x_n\}$ with constants from $K\langle A\rangle$ is $P(X, A) = 0$ with $P \in K\langle A \cup X\rangle$, and a solution is a substitution $x_i \mapsto u_i \in K\langle A\rangle$ making $P$ vanish. The *Diophantine problem* asks, given an equation, whether it has a solution. For the input to be finite, the coefficients are taken from $K_0\langle A\rangle$, where $K_0$ is the prime subfield of $K$ ($\mathbb{Q}$ or $\mathbb{F}_p$).

**Theorem (Kharlampovich and Myasnikov).** For every field $K$ and every nonempty set $A$, the Diophantine problem in $K\langle A\rangle$ with coefficients in $K_0\langle A\rangle$ is undecidable (Theorem 5 and the introduction of arXiv:1606.03617v2). More precisely, the ring $\mathbb{Z}$ is interpretable by equations in $K\langle A\rangle$ when $\operatorname{char} K = 0$, and Denef's structure $\langle \mathbb{Z}; +, \mid_p\rangle$ (the integers with addition and a divisibility-by-powers-of-$p$ relation) is interpretable by equations when $\operatorname{char} K = p > 0$ (Theorem 6 of the same version).

The undecidability does not come from the coefficients alone: when $K$ is finite or algebraically closed, the Diophantine problem in $K$ is decidable, and by Makanin's theorem equations in a free monoid are decidable. The same paper shows that the Diophantine problem in the group algebra $K(G)$ is undecidable for many torsion-free groups $G$, including torsion-free hyperbolic groups and right-angled Artin groups.

## Depends on

- [Field](../../../Algebra/rings-and-fields/field.md)
- [Ring with identity](../../../Algebra/rings-and-fields/ring-with-identity.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The centralizer of a non-invertible element $P \in K\langle A\rangle$ is a polynomial ring $K[t]$ in one variable, and centralizers are defined by equations, so $K[t]$ is interpretable by equations in $K\langle A\rangle$. In characteristic zero Denef's method interprets $\mathbb{Z}$ in $K[t]$ through the polynomial solutions of a Pell equation, and the undecidability of Hilbert's tenth problem over $\mathbb{Z}$ finishes the proof. In characteristic $p$, Denef's theorem interprets $\langle \mathbb{Z}; +, \mid_p\rangle$ in $K[t]$, and the existential theory of that structure is undecidable. Transitivity of interpretations by equations and the reduction of Diophantine problems along them complete the argument. A complete expansion links pages for Denef's interpretations of $\mathbb{Z}$, respectively $\langle \mathbb{Z}; +, \mid_p\rangle$, in polynomial rings $K[t]$ and for the undecidability of positive existential sentences in $\langle \mathbb{Z}; +, \mid_p\rangle$, which have none.

## Sources

- O. Kharlampovich and A. Myasnikov, "Equations in algebras", *International Journal of Algebra and Computation* 28(8):1517–1533, 2018, doi:[10.1142/S0218196718400064](https://doi.org/10.1142/S0218196718400064); read as arXiv:1606.03617v2 ([arXiv](https://arxiv.org/abs/1606.03617v2)), whose numbering is used (each environment has its own counter): the introduction, Theorems 5 and 6 with the section on free associative algebras, and Theorems 8 and 9 and Corollaries 4 and 5 on group algebras.
