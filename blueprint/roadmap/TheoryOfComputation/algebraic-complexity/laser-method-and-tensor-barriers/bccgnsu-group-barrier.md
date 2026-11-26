# Blasiak et al.: slice rank obstructs the group-theoretic approach over bounded-exponent abelian groups

The **slice rank** of a tensor $T \in \mathbb{F}^{X \times Y \times Z}$ is the least $r$ such that $T$ is a sum of $r$ tensors each of the form $f(x) g(y, z)$, $f(y) g(x, z)$ or $f(z) g(x, y)$. For every finite abelian group $G$ of bounded exponent, the group algebra multiplication tensor of $G$ has slice rank at most $|G|^{1 - c}$ for a constant $c > 0$ depending only on the exponent. Consequently the simultaneous triple product property in such groups cannot prove $\omega = 2$: abelian groups of bounded exponent do not yield $\omega = 2$ via the Cohn-Kleinberg-Szegedy-Umans approach.

## Proof sketch

The tensor $\sum_{a + b + c = 0} x_a y_b z_c$ over $\mathbb{F}_p[G]$ with $G = \mathbb{Z}_p^n$ has slice rank $O(\Gamma_p^n)$ with $\Gamma_p < p$, by the Croot-Lev-Pach / Ellenberg-Gijswijt polynomial method as reformulated by Tao. Slice rank lower-bounds the size of any family satisfying the simultaneous triple product property, and such a family with $\omega = 2$ would require slice rank $|G|^{1 - o(1)}$.

## Depends on

- [Strassen's asymptotic spectrum of tensors and asymptotic rank](asymptotic-spectrum.md)
- [Conjecture that the square exponent is two](../matrix-multiplication-exponent/omega-equals-two-conjecture.md)

## Proof depends on

- [Strassen's asymptotic spectrum of tensors and asymptotic rank](asymptotic-spectrum.md)
- [Conjecture that the square exponent is two](../matrix-multiplication-exponent/omega-equals-two-conjecture.md)

## Sources

- J. Blasiak, T. Church, H. Cohn, J. A. Grochow, E. Naslund, W. F. Sawin, C. Umans, "On cap sets and the group-theoretic approach to matrix multiplication", Discrete Analysis (2017), arXiv:1605.06702.
- T. Tao, W. Sawin, "Notes on the slice rank of tensors" (2016); T. Tao, "A symmetric formulation of the Croot-Lev-Pach-Ellenberg-Gijswijt capset bound", blog note (2016).
