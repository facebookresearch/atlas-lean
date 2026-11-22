# Character of the regular representation

Let $V_i$ ($i \in \iota$) be a complete set of irreducible complex representations of a finite
group $G$ (pairwise non-isomorphic irreducible finite-dimensional complex representations, every irreducible finite-dimensional complex representation being isomorphic to one of them), with dimensions $d_i$ and characters $\chi_i$. Then for every $g \in G$

$$\sum_i d_i\, \chi_i(g) = \begin{cases} |G| & g = 1, \\ 0 & g \ne 1. \end{cases}$$

The left side is the character of the regular representation, which contains each irreducible
representation $d_i$ times; Diaconis's proof of Fourier inversion (Saint-Flour notes, Theorem
4.1(a)) rests on this identity, citing Serre. It follows from the completeness of irreducible characters among class functions and their orthonormality: the class function $|G|\,\delta_1$ is a
combination $\sum_i c_i \chi_i$, and pairing with $\chi_j$ gives $c_j = \chi_j(1) = d_j$.

## Sources

- P. Diaconis, *Applications of non-commutative Fourier analysis to probability problems*,
  Saint-Flour lecture notes, Lecture Notes in Math. 1362 (1988), proof of Theorem 4.1(a).
