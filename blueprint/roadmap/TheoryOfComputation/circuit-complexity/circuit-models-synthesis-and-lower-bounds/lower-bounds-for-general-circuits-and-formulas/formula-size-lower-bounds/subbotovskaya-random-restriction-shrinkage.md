# Subbotovskaya's shrinkage under random restrictions

Let $L(f)$ denote De Morgan formula leaf size. For every Boolean function $f$ on $n$ variables and every $1\le k\le n$, if $\rho$ is a random restriction leaving exactly $k$ variables free (chosen uniformly) and fixing the others to independent uniform bits, then

$$
\mathbb{E}_\rho\bigl[L(f|_\rho)\bigr]\le 4\Bigl(\frac{k}{n}\Bigr)^{3/2}L(f)+1.
$$

The key step: fixing one random variable of a leaf-minimal formula with $L\ge 2$ leaves to a random constant removes on average at least $3L/(2n)$ leaves.

## Proof sketch

Fixing variable $x_i$ removes its $\ell_i$ leaves; in a leaf-minimal formula each such leaf feeds a binary gate whose other argument is also removed under one of the two values, giving expected shrinkage $\tfrac32\ell_i$. Averaging over $i$ and iterating $n-k$ times yields the product $\prod_{j=k+1}^n(1-\tfrac{3}{2j})\le 4(k/n)^{3/2}$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- B. A. Subbotovskaya, "Realizations of Linear Functions by Formulas Using ∨, &, −", Soviet Mathematics Doklady 2, 110–112, 1961.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012 (Subbotovskaya's lemma and its probabilistic form: with probability at least $3/4$, $L(f|_\rho)\le 4(k/n)^{3/2}L(f)$).
