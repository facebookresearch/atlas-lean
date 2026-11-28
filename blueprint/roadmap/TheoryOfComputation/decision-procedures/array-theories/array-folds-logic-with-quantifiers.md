# Array folds logic with an ∃\*∀\* quantifier prefix is undecidable

Adding a universally quantified index to array folds logic, that is allowing formulas with an $\exists^*\forall^*$ prefix, makes its satisfiability undecidable, although the quantifier-free logic is PSPACE-complete.

**Theorem.** Satisfiability of [array folds logic](array-folds-logic.md) formulas with an $\exists^*\forall^*$ quantifier prefix over integer variables is undecidable.

The quantifier-free fragment, where all variables are implicitly existential, is decidable and PSPACE-complete. The source also shows that adding a concatenation operator on arrays makes AFL undecidable, by reduction from a theory of concatenation; that extension is not stated here.

## Depends on

- [Array folds logic](array-folds-logic.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Some multi-stack machine has an undecidable halting set](../../computability/halting-problem-and-rice-s-theorem/exists-not-tm2-decidable-tm2-halts-on.md)

## Expansion

The reduction is from Hilbert's tenth problem over the natural numbers, undecidable by the DPRM theorem applied to an undecidable recursively enumerable set. Addition is already available, so it suffices to define multiplication $x=y\cdot z$ by an $\exists^*\forall^*$ formula. The source's formula requires $|a|=x$, uses one fold to say that $a$ is a $0$–$1$ array with exactly $z$ ones, and, for every index $j$ with $0\le j<|a|$, uses a fold starting at $j$ to say that exactly one $1$ occurs among the positions $j,\dots,j+y$ that lie in the array. As printed this does not force $x=y\cdot z$: for $a=(0,0,1)$, $x=3$, $y=2$ and $z=1$ every window holds exactly one $1$, yet $3\ne2\cdot1$, because every start $j$ in the array is tested, but a full window $j,\dots,j+y$ has $y+1$ cells and a window that runs past the end of the array is checked only on its cells inside it. The printed formula in fact holds exactly when $z=\lceil x/(y+1)\rceil$ (and $z=0$ when $x=0$), so it also rejects true products: for $x=2$, $y=1$, $z=2$ the only $0$–$1$ array with two ones is $(1,1)$, whose first window holds two ones. A good expansion replaces the window test by an encoding that pins both array boundaries, for example: either $y=0$ and $x=0$, or $y>0$, $|a|=x$, $a$ is a $0$–$1$ array with exactly $z$ ones, $x>0$ implies $a[x-1]=1$, and for all $j$ with $0\le j<x$, $a[j]=1$ holds exactly when $j+1=y$ or ($j+1>y$ and $a[j-y]=1$). Then the ones sit exactly at the positions $j$ with $y\mid j+1$, the last one forces $y\mid x$, and counting them gives $x=y\cdot z$.

## Sources

- Przemysław Daca, Thomas A. Henzinger and Andrey Kupriyanov, "Array Folds Logic", in *Computer Aided Verification (CAV 2016)*, Lecture Notes in Computer Science, Springer, 2016, pp. 230–248, doi:[10.1007/978-3-319-41540-6_13](https://doi.org/10.1007/978-3-319-41540-6_13); read in arXiv:1603.06850v3 ([arXiv](https://arxiv.org/abs/1603.06850v3)), whose numbering is used: Theorem 2 and its proof in Section 4.1 (Undecidable Extensions), and Corollary 1 for the concatenation operator.
