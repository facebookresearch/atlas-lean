# Existence of cyclic or WNU polymorphisms of a promise template is undecidable

No algorithm decides, given a finite promise template whose first structure has at most three elements, whether its polymorphisms include cyclic ones or weak near-unanimity ones, in any of the usual arity regimes.

For a finite template $(\mathbb A,\mathbb B)$, an $n$-ary polymorphism $f\in\mathrm{Pol}(\mathbb A,\mathbb B)$ (see [the polymorphism minion](polymorphism-minion-of-a-promise-template.md)) with $n\ge2$ is *cyclic* if $f(x_1,\dots,x_n)=f(x_2,\dots,x_n,x_1)$ for all arguments (every unary polymorphism would satisfy this identity, and a template always has one, since $\mathbb A\to\mathbb B$), and *weak near-unanimity* (WNU) if $f(y,x,\dots,x)=f(x,y,x,\dots,x)=\cdots=f(x,\dots,x,y)$ for all $x,y$.

**Theorem (Larrauri).** It is undecidable, given a finite template $(\mathbb A,\mathbb B)$ with $|A|\le3$, whether $\mathrm{Pol}(\mathbb A,\mathbb B)$ contains

1. cyclic polymorphisms (i) of every prime arity, (ii) of at least one arity $n\ge2$, equivalently of some prime arity, (iii) of all but finitely many prime arities, (iv) of infinitely many prime arities;
2. WNU polymorphisms (i) of every arity $k\ge3$, (ii) of at least one arity $k\ge3$, (iii) of all but finitely many arities $k\ge3$, (iv) of infinitely many arities $k\ge3$.

Having a cyclic polymorphism of some arity $n\ge2$ is equivalent to having one of prime arity (the remark before the restatement of Theorem 1.2 in Section 3). For ordinary constraint satisfaction problems ($\mathbb A=\mathbb B$) the source recalls that a cyclic polymorphism exists if and only if a WNU does, that this condition is decidable, and that it characterizes the tractable CSPs if P $\ne$ NP (Bulatov, Zhuk); WNUs of all arities $k\ge3$ characterize the CSPs of bounded width instead.

## Depends on

- [The polymorphism minion Pol(A,B) of a promise template](polymorphism-minion-of-a-promise-template.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces from tiling problems (Propositions 4.2 and 5.3 of the source) with the same method as for the relaxation algorithms, without using that result: it is applied to minions defined by the corresponding minor conditions: the existence of cyclic or WNU elements of the relevant arities is expressed by primitive positive minor conditions, and the templates built from the grid or from growing triangular slices of the grid have such polymorphisms in the required arities iff the tiling instance is solvable, in the "every arity", "some arity", "all but finitely many" and "infinitely many" regimes respectively.

## Sources

- Alberto Larrauri, "Ineffectiveness for Search and Undecidability of PCSP Meta-Problems", in *2025 IEEE 66th Annual Symposium on Foundations of Computer Science (FOCS)*, 2025, pp. 1313–1350, doi:[10.1109/FOCS63196.2025.00070](https://doi.org/10.1109/FOCS63196.2025.00070); read in arXiv:2504.04639v4 ([arXiv](https://arxiv.org/abs/2504.04639v4)), whose numbering is used: Theorem 1.2 (restated in Section 3), Section 2 (minions, cyclic and WNU elements, minor conditions), the subsections of Section 9 on weak near-unanimity and cyclic polymorphisms, and Proposition 5.3.
