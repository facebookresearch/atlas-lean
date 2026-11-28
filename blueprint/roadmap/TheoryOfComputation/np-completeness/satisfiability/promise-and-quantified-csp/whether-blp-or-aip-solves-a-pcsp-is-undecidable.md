# Whether BLP or AIP solves a promise CSP is undecidable

No algorithm decides, given a finite promise template, whether the basic linear programming relaxation, the affine integer relaxation, or their combination solves its promise constraint satisfaction problem; for BLP and AIP this holds already when the first structure has two elements.

For a finite [promise template](promise-csp-of-a-template-pair.md) $(\mathbb A,\mathbb B)$ and an input $\mathbb I$, the $0/1$ system $\mathrm{IP}_{\mathbb A}(\mathbb I)$ has a variable $x_{v,a}$ for each $v\in I$, $a\in A$ and a variable for each pair of an $\mathbb I$-tuple and an $\mathbb A$-tuple in the same relation, with equations stating that each $v$ and each constraint tuple chooses exactly one value and that the choices are consistent; it is satisfiable iff $\mathbb I\to\mathbb A$. The *affine integer programming* algorithm AIP accepts $\mathbb I$ iff the system has a solution over $\mathbb Z$, the *basic linear programming* algorithm BLP iff it has a solution over $[0,1]\cap\mathbb Q$, and BLP+AIP combines the two (Brakensiek, Guruswami, Wrochna and Živný). An algorithm *solves* $\mathrm{PCSP}(\mathbb A,\mathbb B)$ if it accepts every $\mathbb I$ with $\mathbb I\to\mathbb A$ and rejects every $\mathbb I$ with $\mathbb I\not\to\mathbb B$.

**Theorem (Larrauri).** Let $\mathcal S^{\mathcal Q}_k$ be the family of finite templates $(\mathbb A,\mathbb B)$ with $|A|\le k$ such that the algorithm $\mathcal Q$ solves $\mathrm{PCSP}(\mathbb A,\mathbb B)$.
1. $\mathcal S^{\mathrm{AIP}}_2$ and $\mathcal S^{\mathrm{BLP}}_2$ are undecidable (Theorems 3.1 and 3.2).
2. $\mathcal S^{\mathrm{BLP+AIP}}_5$ is undecidable (Theorem 3.3).
3. There is a template in $\mathcal S^{\mathrm{AIP}}_2$, and one in $\mathcal S^{\mathrm{BLP}}_2$, for which no computable minion homomorphism from the corresponding algorithm's minion to the [polymorphism minion](polymorphism-minion-of-a-promise-template.md) $\mathrm{Pol}(\mathbb A,\mathbb B)$ exists, although some minion homomorphism exists.

By Theorem 2.1 (Barto, Bulín, Krokhin and Opršal; Brakensiek et al.), $\mathcal Q$ solves $\mathrm{PCSP}(\mathbb A,\mathbb B)$ iff there is a minion homomorphism $\mathscr M_{\mathcal Q}\to\mathrm{Pol}(\mathbb A,\mathbb B)$, where $\mathscr M_{\mathrm{AIP}}$ consists of integer tuples and $\mathscr M_{\mathrm{BLP}}$ of rational stochastic vectors summing to $1$, minors adding coordinates. Item 3 means that for these templates no algorithm turns an accepted relaxation solution into a homomorphism $\mathbb I\to\mathbb B$ by a fixed computable rounding of this form; the source also shows the corresponding search (rounding) problems are TFNP-hard on templates with $|A|\le4$ (AIP) or $|A|\le5$ (BLP, BLP+AIP).

## Depends on

- [Promise constraint satisfaction PCSP(A,B) for a pair of finite templates](promise-csp-of-a-template-pair.md)
- [The polymorphism minion Pol(A,B) of a promise template](polymorphism-minion-of-a-promise-template.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Minions, minion homomorphisms and pp-constructions](../finite-domain-csp-dichotomy/minions-minion-homomorphisms-pp-constructions.md)

## Proof depends on

- [The tiling problem is undecidable](../../../undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The reductions start from tiling problems: for the quarter-plane grid structure $\Gamma$ (origin, horizontal and vertical successor relations), the set of finite structures $\mathbb T$ with $\Gamma\to\mathbb T$ is undecidable (Wang's origin-constrained tiling), and some such $\mathbb T$ admit no computable homomorphism (Hanf); a three-dimensional grid with doubling relations gives TFNP-hardness, and growing triangular slices of the grid give the variants with all but finitely many or infinitely many arities. The core of the proof builds, from a structure $\mathbb G$ of this kind and a minion $\mathscr M$ with a finite *description* (a finite family of pp-definable subsets), finite templates $(\mathbb A,\mathbb B)$ whose polymorphism minion, restricted to suitably large arities, encodes homomorphisms $\mathbb G\to\mathbb T$, so that $\mathscr M\to\mathrm{Pol}(\mathbb A,\mathbb B)$ iff $\mathbb G\to\mathbb T$. Instantiating $\mathscr M$ with $\mathscr M_{\mathrm{AIP}}$, $\mathscr M_{\mathrm{BLP}}$ or $\mathscr M_{\mathrm{BLP+AIP}}$ and bounding the size of $A$ gives the theorem.

## Sources

- Alberto Larrauri, "Ineffectiveness for Search and Undecidability of PCSP Meta-Problems", in *2025 IEEE 66th Annual Symposium on Foundations of Computer Science (FOCS)*, 2025, pp. 1313–1350, doi:[10.1109/FOCS63196.2025.00070](https://doi.org/10.1109/FOCS63196.2025.00070); read in arXiv:2504.04639v4 ([arXiv](https://arxiv.org/abs/2504.04639v4)), whose numbering is used: Section 2 (the systems, the algorithms AIP, BLP and BLP+AIP, minions, and Theorem 2.1), Theorems 3.1–3.3, Theorem 4.1 and the overview of Section 4, Proposition 4.2 (the grid), and Section 5 (Propositions 5.2 and 5.3 on the doubling grid and on triangles).
