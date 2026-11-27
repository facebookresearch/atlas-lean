# Array folds logic with an ∃*∀* quantifier prefix is undecidable

Adding a universally quantified index to array folds logic, that is allowing formulas with an $\exists^*\forall^*$ prefix, makes its satisfiability undecidable, although the quantifier-free logic is PSPACE-complete.

**Theorem.** Satisfiability of [array folds logic](array-folds-logic.md) formulas with an $\exists^*\forall^*$ quantifier prefix over integer variables is undecidable.

The quantifier-free fragment, where all variables are implicitly existential, is decidable and PSPACE-complete. The source also shows that adding a concatenation operator on arrays makes AFL undecidable, by reduction from a theory of concatenation; that extension is not stated here.

## Depends on

- [Array folds logic](array-folds-logic.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The reduction is from Hilbert's tenth problem. Addition is already available, so it suffices to define multiplication $x=y\cdot z$ by an $\exists^*\forall^*$ formula. The formula requires $|a|=x$, uses one fold to say that $a$ is a $0$–$1$ array with exactly $z$ ones, and, for every index $j$ with $0\le j<|a|$, a fold starting at $j$ that counts exactly one $1$ among the positions $j,\dots,j+y$. This forces $a$ to consist of $z$ blocks $0\cdots01$ of length $y$, so $x=y\cdot z$.

## Sources

- Przemysław Daca, Thomas A. Henzinger and Andrey Kupriyanov, "Array Folds Logic", in *Computer Aided Verification (CAV 2016)*, Lecture Notes in Computer Science, Springer, 2016, pp. 230–248, doi:[10.1007/978-3-319-41540-6_13](https://doi.org/10.1007/978-3-319-41540-6_13); read in arXiv:1603.06850v3 ([arXiv](https://arxiv.org/abs/1603.06850v3)), whose numbering is used: Theorem 2 and its proof in Section 4.1 (Undecidable Extensions), and Corollary 1 for the concatenation operator.
