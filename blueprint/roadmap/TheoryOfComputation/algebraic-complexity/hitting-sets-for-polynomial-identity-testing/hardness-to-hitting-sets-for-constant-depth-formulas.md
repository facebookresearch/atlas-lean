# Kabanets–Impagliazzo: hardness gives hitting sets for constant-depth formulas

Let $f$ be a multilinear polynomial in $m$ variables of degree at most $d$, and $S_1,\dots,S_n\subseteq L$ an $(m,a)$-design. Over a field of characteristic zero, if $f$ has no unbounded fan-in formula of product-depth $\Delta+2$ with at most $\mathrm{poly}(s\,2^a(a+1),d)$ nodes, then the values of $\mathrm{NW}_f$ on the grid $\{0,1,\dots,sd\}^{L}$ form a hitting set for the $n$-variate polynomials computed by formulas of product-depth $\Delta$ with at most $s$ nodes.

## Proof sketch

If a small formula $C$ vanishes on the generator's image, a hybrid argument finds an index $i$ and a fixing of the other seed variables such that $C$ with the first $i-1$ outputs substituted vanishes when $y_i=f(z|_{S_i})$ but not identically; so $f$ is a root of a small formula in $y_i$ whose other inputs depend on at most $a$ variables of $S_i$ each, and by the root lemma $f$ has a small formula of product-depth $\Delta+2$, a contradiction.

## Depends on

- [The Nisan–Wigderson generator for polynomials](nisan-wigderson-generator-for-polynomials.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](../constant-depth-algebraic-circuits/unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Roots of constant product-depth formulas have small formulas](../constant-depth-algebraic-circuits/roots-of-constant-depth-formulas.md)
- [Combinatorial Nullstellensatz, Theorem 1.2](../../../Combinatorics/additive-combinatorics/combinatorial-nullstellensatz/exists-eval-ne-zero.md)

## Sources

- Valentine Kabanets, Russell Impagliazzo, "Derandomizing Polynomial Identity Tests Means Proving Circuit Lower Bounds", Computational Complexity, 2004.
- Chi-Ning Chou, Mrinal Kumar, Noam Solomon, "Closure Results for Polynomial Factorization", Theory of Computing, 2019.
- Somnath Bhattacharjee, Mrinal Kumar, Shanthanu S. Rai et al., "Closure under factorization from a result of Furstenberg", 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 2026.
