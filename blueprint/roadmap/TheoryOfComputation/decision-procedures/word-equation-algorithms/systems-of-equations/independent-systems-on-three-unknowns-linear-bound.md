# Independent systems on three unknowns with a nonperiodic solution are linearly bounded by their equations

An independent system of constant-free word equations in three unknowns that has a nonperiodic solution has at most $|E_i| + |E_j| + 1$ equations, for any two of its equations $E_i, E_j$. These bounds depend on the lengths of the equations.

Let $\Xi = \{x_1, x_2, x_3\}$ and let $E_1, \dots, E_m$, $m \ge 1$, be an [independent system](independent-systems-of-word-equations.md) of constant-free word equations over $\Xi$ that has a nonperiodic solution. Then

1. $m \le |E_i| + |E_j| + 1$ for any two distinct equations $E_i, E_j$ of the system, and
2. $m \le 2 \big( |E_1|_x + |E_1|_y \big) + 1$ for any two distinct unknowns $x, y \in \Xi$.

Here $|E| = |uv|$ and $|E|_x = |uv|_x$ for $E = (u, v)$, counting both sides. For $m = 1$ item 1 is vacuous and item 2 is immediate. These are Holub and Žemlička's length-dependent bounds. Independently of the lengths, $m \le 17$ ([Independent systems on three unknowns with a nonperiodic solution have at most 17 equations](independent-systems-on-three-unknowns-are-bounded.md)).

## Depends on

- [Independent systems of constant-free word equations](independent-systems-of-word-equations.md)

## Proof depends on

None.

## Expansion

Words over positive integers are encoded by polynomials, $P(a_1 \cdots a_\ell) = \sum_t a_t X^{t-1}$, with positive letter codes so that the encoding is injective, and an equation $E = (u, v)$ in $n$ unknowns gives the polynomials $S_{E, x_j} \in \mathbb{Z}[X_1, \dots, X_n]$, a signed sum of one monomial for each occurrence of $x_j$ in $u$ or in $v$; for a length type $L = (|h(x_1)|, \dots, |h(x_n)|)$, $S_{E, x_j}(L)$ denotes the univariate polynomial obtained by substituting $X^{L_i}$ for $X_i$, and $h$ solves $E$ exactly when $\sum_j S_{E, x_j}(L)\, P(h(x_j)) = 0$. For two strongly independent equations $E, E'$ (each proper subsystem has a solution of rank $n - 1$ that is not a solution of the whole), some minor $t_{k\ell} = S_{E, x_k} S_{E', x_\ell} - S_{E', x_k} S_{E, x_\ell}$ is nonzero. For each common solution of rank $n - 1$, with letter-count vectors spanning the hyperplane with coprime normal $\lambda$, the irreducible binomial $\mathbf{X}^{\lambda_+} - \mathbf{X}^{\lambda_-}$ divides $t_{k\ell}$, and linearly nonequivalent solutions give non-associated binomials. Counting degrees, bounded by $|E| + |E'|$ since each occurrence on either side contributes one monomial, and counting minimal monomials, at most $2(|E|_{x_k} + |E|_{x_\ell})$, bounds the number $m'$ of pairwise linearly nonequivalent common solutions of rank $n - 1$ (Holub and Žemlička, Theorem 19). In a strongly independent system $T = \{E_1, \dots, E_m\}$, the witnesses for $E_3, \dots, E_m$ are $m - 2$ pairwise linearly nonequivalent common solutions of $E_1$ and $E_2$; a solution of rank $n - 1$ of the whole system is linearly nonequivalent to all of them and gives the extra class, so $m - 1 \le m'$ (Theorem 21). For three unknowns, solutions of rank $2$ are exactly the nonperiodic ones. The counting argument is needed only for systems with at least three equations; for $m \le 2$ the source calls the bounds trivial, and the balance step below must not be applied to a single equation: $\{xz = yz\}$ is independent and unbalanced and has the nonperiodic solution $x, y \mapsto a$, $z \mapsto b$. In a strongly independent system with at least two equations and a solution of rank $n - 1$, every equation is balanced: that solution solves each pair $E_i, E_j$, so if $E_i$ were unbalanced, its solutions of rank $n - 1$ would all solve $E_j$ (Saarela, European Journal of Combinatorics 47 (2015), Theorem 6.1), against the witness of rank $n - 1$ for $E_j$, which solves $E_i$ but not $E_j$. For balanced equations the three minors are $t \cdot (X_1 - 1, X_2 - 1, X_3 - 1)$ for one polynomial $t$, so every pair of unknowns gives a nonzero minor (Corollary 23).

This page becomes ready once the following are pages of their own: the polynomial encoding of word equations, strongly independent systems, the bound on common solutions of rank $n - 1$ (Theorem 19, with Lemmas 11, 12, 16, 17 and 18), the bound on strongly independent systems (Theorem 21, with Lemma 20), the balance of equations in such systems (Saarela, European Journal of Combinatorics 47 (2015), Theorem 6.1), Corollary 23, and the rank of a solution together with the defect step identifying the rank-two solutions in three unknowns with the nonperiodic ones (Holub and Žemlička, Section 2, Lemmas 2 and 15).

## Sources

- Štěpán Holub, Jan Žemlička, "Algebraic properties of word equations", Journal of Algebra 434 (2015), 283–301, https://doi.org/10.1016/j.jalgebra.2015.03.021; read as arXiv:1403.1951v2, https://arxiv.org/abs/1403.1951v2, Corollary 24 (Section 4), with Theorems 19 and 21, Lemmas 17, 18 and 20 and Corollary 23 for the proof; the polynomials $S_{E,x}$ are defined in Section 3, and Lemma 18 counts monomials coming from both sides of $E$
- Aleksi Saarela, "Systems of word equations, polynomials and linear algebra: A new approach", European Journal of Combinatorics 47 (2015), 1–14, https://doi.org/10.1016/j.ejc.2015.01.005; read as arXiv:1401.7498v1, https://arxiv.org/abs/1401.7498v1, Corollary 6.4 (Section 6), the earlier quadratic bound, and Theorem 6.1 on unbalanced equations
- Dirk Nowotka and Aleksi Saarela, "An Optimal Bound on the Solution Sets of One-Variable Word Equations and its Consequences", ICALP 2018, LIPIcs 107, Article 136 (2018), https://doi.org/10.4230/LIPIcs.ICALP.2018.136, Theorem 26 (the length-independent bound $17$)
