# Total search problems are not FNP-hard unless NP = coNP

If some search problem $R' \in \mathsf{TFNP}$ is $\mathsf{FNP}$-hard under reductions $(f, g)$ that may also report "no solution" (for every $x$ and every solution $y'$ of $f(x)$, $g(x, y')$ is a solution of $x$ when $x$ has one, and is the answer "no" otherwise), then $\mathsf{NP} = \mathsf{coNP}$. Indeed, applied to the satisfiability search problem, a solution $y'$ of $f(\varphi)$ with $g(\varphi, y') = \text{no}$ is a polynomial-size, polynomial-time checkable certificate that $\varphi$ is unsatisfiable, and such a $y'$ exists for every unsatisfiable $\varphi$ by totality of $R'$.

## Depends on

- [Search problems: FNP, FP and TFNP](search-problems-fnp-fp-and-tfnp.md)

## Proof depends on

- [UNSAT is coNP-complete](../../completeness-other-classes/unsatisfiability/unsat-conp-complete.md)
- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- N. Megiddo and C. H. Papadimitriou, "On total functions, existence theorems and computational complexity", *Theoretical Computer Science* 81:317–324, 1991, <http://theory.stanford.edu/~megiddo/pdf/papadimX.pdf>
- T. Roughgarden, *Stanford CS364A Algorithmic Game Theory*, Lecture 20, 2013, <https://theory.stanford.edu/~tim/f13/l/l20.pdf>, Theorem 3.1
