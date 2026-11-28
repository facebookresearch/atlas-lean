# Independent systems on three unknowns with a nonperiodic solution have at most 17 equations

An independent system of constant-free word equations in three unknowns that has a nonperiodic solution has at most 17 equations, whatever the lengths of the equations.

Let $\Xi = \{x, y, z\}$ and let $\Sigma$ be an alphabet. If a system of constant-free word equations over $\Xi$ is [independent](independent-systems-of-word-equations.md), that is, not equivalent to any of its proper subsystems with respect to morphisms $h : \Xi^* \to \Sigma^*$, and has a nonperiodic solution $h : \Xi^* \to \Sigma^*$, then it has at most $17$ equations. In the notation of independent systems, $\mathrm{IS}'(3) \le 17$.

## Depends on

- [Independent systems of constant-free word equations](independent-systems-of-word-equations.md)

## Proof depends on

- [One-variable equations have at most three or infinitely many solutions](../../word-equations-with-length/one-variable-solution-sets-at-most-three.md)

## Expansion

The source proves the theorem in one line from two results. The first is the bound on one-variable equations: a word equation in one variable with constants has either infinitely many solutions or at most three (Theorem 25 of the source). The second is an earlier result of the same authors, stated in the source as its Theorem 8 and proved in their paper in the International Journal of Foundations of Computer Science: if every one-variable word equation has either infinitely many solutions or at most three, then every independent system of constant-free three-variable equations with a nonperiodic solution has at most $17$ equations. That connection rests on the description of three-generator subsemigroups of a free semigroup by L. G. Budkina and Al. A. Markov, or a similar result of J.-C. Spehner.

The source adds two remarks. Without the requirement of a nonperiodic solution the size can be at most one larger, so $\mathrm{IS}(3) \le 18$. The system $xyz = zyx$, $xyyz = zyyx$ is independent and has the nonperiodic solution $x \mapsto a$, $y \mapsto b$, $z \mapsto a$, so the maximal size of an independent system with a nonperiodic solution lies between $2$ and $17$; the source names improving $17$ as an open problem.

This page becomes ready once the implication of the second result (Nowotka and Saarela, International Journal of Foundations of Computer Science 29(5) (2018), 935–950; Theorem 8 of the source) is a page of its own.

## Sources

- Dirk Nowotka and Aleksi Saarela, "An Optimal Bound on the Solution Sets of One-Variable Word Equations and its Consequences", ICALP 2018, LIPIcs 107, Article 136 (2018), https://doi.org/10.4230/LIPIcs.ICALP.2018.136, Theorem 26 and its proof, Theorem 25, Theorem 8, Example 2, Section 1 (the remark on systems without a nonperiodic solution) and Section 8
- Dirk Nowotka and Aleksi Saarela, "One-Variable Word Equations and Three-Variable Constant-Free Word Equations", International Journal of Foundations of Computer Science 29(5) (2018), 935–950, https://doi.org/10.1142/S0129054118420121, the source of Theorem 8 above
