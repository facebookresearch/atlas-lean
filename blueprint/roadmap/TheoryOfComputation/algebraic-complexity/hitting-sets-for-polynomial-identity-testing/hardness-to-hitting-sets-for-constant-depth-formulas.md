# Kabanets–Impagliazzo: hardness gives hitting sets for constant-depth formulas

Let $F$ be a field of characteristic $0$ or large enough, and fix a depth $\Delta > 0$, where the depth of an unbounded fan-in arithmetic circuit is the number of its alternating sum and product layers. Suppose an explicit family $(f_m)_{m \ge 0}$ of polynomials, $f_m$ in $m$ variables with $\deg(f_m) \le m$, requires circuits of depth $\Delta$ and size $B(m)$. Then there is a family $(H_n)$ of explicit hitting sets for the polynomials computed by polynomial-size circuits of depth at most $\Delta - O(1)$, in particular by such formulas, with

$$|H_n| = n^{O\left((B^{-1}(n))^2/\log n\right)}.$$

In particular, if $B(m) = m^{\omega(1)}$, then $|H_n| \le n^{O(n^{\varepsilon})}$ for every $\varepsilon > 0$.

## Proof sketch

Use the Kabanets–Impagliazzo generator: substitute the hard polynomial on the sets of a combinatorial design into a small circuit and evaluate on a grid. If a small nonzero circuit $C$ vanishes under the substitution, a hybrid argument finds an index $i$ and a fixing of the seed variables outside the $i$-th design set such that a polynomial $P(z,y)$ obtained from $C$ is nonzero while $P(z, f(z|_{S_i})) = 0$; so $y - f(z|_{S_i})$ divides $P$, and closure of constant-depth circuits under taking such factors gives a circuit for $f$ of depth $\Delta$ and size below $B$, a contradiction. A nonzero polynomial of low degree does not vanish on a large enough grid. (Derived, not stated in this form by the sources: running the argument for formulas over an $(m,a)$-design gives an absolute constant $c_0$ and an absolute polynomial $q$ such that, over characteristic zero, if a multilinear $f$ in $m$ variables of degree at most $d$ has no circuit of product-depth at most $\Delta+c_0$ with at most $q(s\,2^a(a+1),d,m)$ nodes, then the values of $\mathrm{NW}_f$ on the grid $\{0,1,\dots,sd\}^{L}$ hit every nonzero $n$-variate polynomial computed by a formula of product-depth at most $\Delta$ with at most $s$ nodes.)

## Depends on

- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](../constant-depth-algebraic-circuits/unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [The Nisan–Wigderson generator for polynomials](nisan-wigderson-generator-for-polynomials.md)
- [Roots of constant product-depth formulas have small formulas](../constant-depth-algebraic-circuits/roots-of-constant-depth-formulas.md)
- [Combinatorial Nullstellensatz, Theorem 1.2](../../../Combinatorics/additive-combinatorics/combinatorial-nullstellensatz/exists-eval-ne-zero.md)

## Sources

- Somnath Bhattacharjee, Mrinal Kumar, Shanthanu S. Rai, Varun Ramanathan, Ramprasad Saptharishi, Shubhangi Saraf, "Closure under factorization from a result of Furstenberg", 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 2026; arXiv:2506.23214, Section 6.1, Theorem 6.1.
- Valentine Kabanets, Russell Impagliazzo, "Derandomizing Polynomial Identity Tests Means Proving Circuit Lower Bounds", Computational Complexity, 2004.
- Chi-Ning Chou, Mrinal Kumar, Noam Solomon, "Closure Results for Polynomial Factorization", Theory of Computing, 2019.
