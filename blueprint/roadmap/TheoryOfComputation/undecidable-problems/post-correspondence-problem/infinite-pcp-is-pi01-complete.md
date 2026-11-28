# The infinite Post correspondence problem is Π⁰₁-complete

Deciding whether two morphisms agree on some infinite word is $\Pi^0_1$-complete, so the infinite Post correspondence problem has exactly the dual complexity of the finite one, which is $\Sigma^0_1$-complete.

Instances are pairs $(h,g)$ of morphisms $h,g:A^*\to B^*$ of free monoids, and $(h,g)$ has an *infinite solution* if some $\omega\in A^\omega$ has $h(u)$ and $g(u)$ comparable (one a prefix of the other) for every finite prefix $u$ of $\omega$; see [the infinite Post correspondence problem](the-infinite-post-correspondence-problem.md).

**Theorem.** The set of nonerasing instances of the infinite Post correspondence problem ($\omega\mathrm{PCP}$), those with $h(a) \neq \varepsilon$ and $g(a) \neq \varepsilon$ for every letter $a \in A$, that have an infinite solution, coded as a set of natural numbers, is $\Pi^0_1$-complete: it belongs to the class $\Pi^0_1$, and every $\Pi^0_1$ set of natural numbers is many-one reducible to it, that is, reduces to it by a total computable function.

The restriction follows Finkel, who defines the $\omega$-PCP for two $n$-tuples $(x_1, \dots, x_n)$ and $(y_1, \dots, y_n)$ of nonempty words (Section 3 of arXiv:1107.5886v1), that is, for nonerasing morphisms, while the linked definition page also allows erasing morphisms. Consequently $\omega\mathrm{PCP}$ for nonerasing instances is co-recursively enumerable but not recursively enumerable, while the [Post correspondence problem](pcp.md) itself is $\Sigma^0_1$-complete; both lie at the first level of the arithmetical hierarchy.

## Depends on

- [The infinite Post correspondence problem](the-infinite-post-correspondence-problem.md)
- [The arithmetical class $\Pi_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Co-recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

A solution of the finite problem is a finite witness that can be checked, which puts the PCP in $\Sigma^0_1$; for $\omega\mathrm{PCP}$ the roles reverse, so that despite asking for an infinite object it is no more complex than the PCP. Undecidability of $\omega\mathrm{PCP}$ was known before, already for small instances ([the infinite PCP is undecidable for instances of size 9](the-infinite-post-correspondence-problem-is-unde.md)). The bi-infinite variant, in contrast, sits at the second level of the arithmetical hierarchy ([the bi-infinite PCP is in Σ⁰₂ but not in Π⁰₁](bi-infinite-pcp-is-in-sigma02-not-pi01.md)).

## Sources

- Olivier Finkel, "The exact complexity of the infinite Post Correspondence Problem", *Information Processing Letters* 115(6–8), 2015, pp. 609–611, doi:[10.1016/j.ipl.2015.02.009](https://doi.org/10.1016/j.ipl.2015.02.009), the original proof; not read (its open-access copy on HAL was unreachable), cited beside the source below.
- Olivier Finkel, Vesa Halava, Tero Harju and Esa Sahla, "On bi-infinite and conjugate post correspondence problems", *RAIRO - Theoretical Informatics and Applications* 57 (2023), article 7, doi:[10.1051/ita/2023008](https://doi.org/10.1051/ita/2023008); read in arXiv:2111.04484v3 ([arXiv](https://arxiv.org/abs/2111.04484v3)), which states the result as established: the introduction (the variants of the PCP and the statement that the infinite PCP is $\Pi^0_1$-complete while the PCP is $\Sigma^0_1$-complete, citing the paper above).
- Olivier Finkel, "Three applications to rational relations of the high undecidability of the infinite Post correspondence problem in a regular ω-language", read in arXiv:1107.5886v1 ([arXiv](https://arxiv.org/abs/1107.5886v1)): Section 3, which defines the instances of the $\omega$-PCP as pairs of $n$-tuples of nonempty words.
