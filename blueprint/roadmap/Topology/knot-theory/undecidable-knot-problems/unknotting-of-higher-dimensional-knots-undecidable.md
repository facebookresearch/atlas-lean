# Unknotting of n-dimensional knots is undecidable for n at least three

For every $n \ge 3$ there is no algorithm that decides whether a given smooth $n$-dimensional knot $S^n \subset \mathbb{R}^{n+2}$ is unknotted; consequently the equivalence problem for $n$-knots is undecidable. For classical knots both problems are decidable.

An $n$-*dimensional knot* is a smooth embedding of $S^n$ in $\mathbb{R}^{n+2}$ (or $S^{n+2}$). Two knots are *equivalent* if an ambient isotopy carries one to the other, and a knot is *unknotted* if it is equivalent to the standard embedding of $S^n$ as the unit sphere in a hyperplane of $\mathbb{R}^{n+2}$.

**Theorem (Nabutovsky–Weinberger).** For every $n \ge 3$ there is no algorithm that decides whether a given $n$-dimensional knot is unknotted. Since unknotting is a subproblem of equivalence, the equivalence problem for $n$-dimensional knots is undecidable for $n \ge 3$.

Conventions: the dimension $n$ is fixed and the knot is the input. For classical knots the survey read gives the input format, a finite sequence of distinct points of $\mathbb{Q}^3$ joined by segments; for $n \ge 3$ it gives none, and the format is that of Nabutovsky and Weinberger's paper, which is not restated there. For classical knots ($n = 1$), Haken gave an algorithm deciding unknotting and, with Hemion's completion, equivalence; the equivalence problem for $2$-dimensional knots is left open by Nabutovsky and Weinberger.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The survey read states the theorem and its consequence for equivalence without proof; the proof is in the original paper of Nabutovsky and Weinberger, which shows that the triviality problem for $n$-dimensional knots is algorithmically unsolvable for $n \ge 3$. For classical knots the survey records Haken's algorithm for unknotting, completed by Hemion for equivalence, and it lists the equivalence problem for $2$-dimensional knots as open.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where the definitions, the statement and the classical and $2$-dimensional cases are in Section 7.3 ("Knot theory").
- Alexander Nabutovsky and Shmuel Weinberger, *Algorithmic unsolvability of the triviality problem for multidimensional knots*, Comment. Math. Helv. 71 (1996), no. 1, 426–434, https://doi.org/10.1007/BF02566428, the original source, cited beside the survey read above.
