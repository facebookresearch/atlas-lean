# The uniform distribution has zero Fourier transform at non-trivial irreducibles

Let $\rho$ be an irreducible representation of a finite group $G$ on a finite-dimensional complex
vector space, and suppose some $\rho(g)$ is not the identity. Then the Fourier transform of the
uniform distribution $U(s) = 1/|G|$ at $\rho$ is zero:

$$\hat U(\rho) = \frac{1}{|G|} \sum_{s} \rho(s) = 0 .$$

Proof: $S = \sum_s \rho(s)$ commutes with every $\rho(h)$, so it is a scalar $c$ by Schur's lemma;
and $\rho(h) S = S$ for every $h$, so $c \ne 0$ would force every $\rho(h)$ to be the identity.
Diaconis derives the same fact from the orthogonality of matrix coefficients (Serre, Proposition 4).

## Sources

- P. Diaconis, *Applications of non-commutative Fourier analysis to probability problems*,
  Saint-Flour lecture notes, Lecture Notes in Math. 1362 (1988), Lemma 4.1.
