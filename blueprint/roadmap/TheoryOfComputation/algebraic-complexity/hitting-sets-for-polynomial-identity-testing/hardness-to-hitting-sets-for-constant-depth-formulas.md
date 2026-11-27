# Kabanets–Impagliazzo: hardness gives hitting sets for constant-depth formulas

Over a field of characteristic zero there are an absolute constant $c_0$ and an absolute polynomial $q$ such that the following holds. Let $f$ be a multilinear polynomial in $m$ variables of degree at most $d$, and $S_1,\dots,S_n\subseteq L$ an $(m,a)$-design. If $f$ has no unbounded fan-in circuit of product-depth at most $\Delta+c_0$ with at most $q\bigl(s\,2^a(a+1),d,m\bigr)$ nodes, then the values of $\mathrm{NW}_f$ on the grid $\{0,1,\dots,sd\}^{L}$ form a hitting set for the $n$-variate polynomials computed by unbounded fan-in formulas of product-depth at most $\Delta$ with at most $s$ nodes.

## Proof sketch

A formula with $s$ nodes computes a polynomial of degree at most $s$, so $C\circ\mathrm{NW}_f$ has degree at most $sd$ and, if nonzero, does not vanish on the grid. If a small formula $C$ is nonzero but $C\circ\mathrm{NW}_f=0$, a hybrid argument finds an index $i$ and a fixing of the seed variables outside $S_i$ such that $P(z,y)=C(f(z|_{S_1}),\dots,f(z|_{S_{i-1}}),y,\dots)$ is nonzero while $P(z,f(z|_{S_i}))=0$; each other substituted output depends on at most $a$ variables of $S_i$ and so has a sum-of-products formula with at most $2^a(a+1)+1$ nodes. Then $P$ has a formula of product-depth $\Delta+1$ and size $O(s\,2^a(a+1))$, and by the root lemma $f$ has a circuit of product-depth $\Delta+O(1)$ and size polynomial in $s\,2^a(a+1)$, $d$ and $m$, a contradiction.

## Depends on

- [The Nisan–Wigderson generator for polynomials](nisan-wigderson-generator-for-polynomials.md)
- [Unbounded fan-in arithmetic formulas and circuits of bounded product-depth](../constant-depth-algebraic-circuits/unbounded-fan-in-formulas-and-product-depth.md)

## Proof depends on

- [Roots of constant product-depth formulas have small formulas](../constant-depth-algebraic-circuits/roots-of-constant-depth-formulas.md)
- [Combinatorial Nullstellensatz, Theorem 1.2](../../../Combinatorics/additive-combinatorics/combinatorial-nullstellensatz/exists-eval-ne-zero.md)

## Sources

- Valentine Kabanets, Russell Impagliazzo, "Derandomizing Polynomial Identity Tests Means Proving Circuit Lower Bounds", Computational Complexity, 2004.
- Chi-Ning Chou, Mrinal Kumar, Noam Solomon, "Closure Results for Polynomial Factorization", Theory of Computing, 2019.
- Somnath Bhattacharjee, Mrinal Kumar, Shanthanu S. Rai, Varun Ramanathan, Ramprasad Saptharishi, Shubhangi Saraf, "Closure under factorization from a result of Furstenberg", 58th Annual ACM Symposium on Theory of Computing (STOC 2026), 2026; arXiv:2506.23214, Theorem 6.1.
