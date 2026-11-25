# Fourier transform of a class function at an irreducible representation

Let $\rho$ be an irreducible representation of a finite group $G$ on a finite-dimensional complex
vector space of dimension $d_\rho$, with character $\chi_\rho$. If $P : G \to \mathbb{C}$ is constant on
conjugacy classes, $P(h g h^{-1}) = P(g)$, then

$$\hat P(\rho) = \Bigl(\frac{1}{d_\rho} \sum_{s \in G} P(s)\, \chi_\rho(s)\Bigr) I .$$

Diaconis and Shahshahani write the same sum grouped by conjugacy classes,
$\frac{1}{d_\rho} \sum_i P_i\, n_i\, \chi_i$. Proof: $\hat P(\rho)$ commutes with every $\rho(h)$
(reindex by conjugation), hence is a scalar by Schur's lemma; take traces.

This is what makes conjugation-invariant walks, such as random transpositions, tractable: their
transforms are scalars, and convolution powers become powers of numbers.

## Sources

- P. Diaconis and M. Shahshahani, *Generating a random permutation with random transpositions*,
  Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, Lemma 5.
