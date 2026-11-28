# PSPACE fragments of straight-line replaceAll

Bounding how replaceAll terms nest in the dependency graph of a replaceAll-only formula brings satisfiability from the known EXPSPACE upper bound down to PSPACE-complete: bounded diamond index with single-letter patterns, bounded l-length with constant-string patterns, and l-length at most one with regular-expression patterns.

Let $C$ be a replaceAll-only formula of [straight-line replaceAll constraints](straight-line-replaceall-constraints.md) (concatenation and constant arguments eliminated as described there) whose patterns are regular expressions, with dependency graph $G_C$: an l-edge from each assigned variable to its subject and an r-edge to its replacement, two distinct edges even when subject and replacement coincide.

- A *diamond* in $G_C$ is a pair of distinct paths from a vertex $z$ to a vertex $z' \neq z$ that share no vertex other than $z$ and $z'$; $z$ is its source and $z'$ its destination. A diamond with source $z_2$ is *reachable* from a diamond with destination $z_1'$ if $z_2$ is reachable from $z_1'$ (possibly $z_2 = z_1'$). The *diamond index* $\mathrm{Idx}(G_C)$ is the maximum length $n$ of a sequence $\Delta_1, \dots, \Delta_n$ of diamonds in which each $\Delta_{i+1}$ is reachable from $\Delta_i$, and $0$ if there is no diamond.
- The *l-length* of a path is its number of l-edges, and the *l-length* $\mathrm{Len}(G_C)$ of $G_C$ is the maximum l-length of its paths, $0$ if there are no edges.

Every diamond uses an l-edge, so $\mathrm{Idx}(G_C) \le \mathrm{Len}(G_C)$. For every constant $c$, satisfiability is [PSPACE](../../complexity-classes/time-and-space-complexity-classes/pspace.md)-complete for each of the following fragments:

1. the single-letter case with $\mathrm{Idx}(G_C) \le c$;
2. the constant-string case with $\mathrm{Len}(G_C) \le c$;
3. the regular-expression case with $\mathrm{Len}(G_C) \le 1$.

The bounds refer to the replaceAll-only formula. A graph that ignored concatenation would be wrong: the EXPSPACE-hardness construction of Chen, Hague, Lin, Rümmer and Wu (2019, with automata-given constraints) alternates single-letter replaceAll with concatenation, and only after concatenation is expressed by replaceAll do its layers produce long chains of l-edges and many diamonds.

## Depends on

- [Straight-line replaceAll constraints](straight-line-replaceall-constraints.md)
- [The complexity class PSPACE](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Savitch's theorem](../../complexity-classes/savitch.md)

## Expansion

This node still needs its proof broken down. Path counting (Proposition 4.5): between two vertices of $G_C$ there are at most $(|\mathrm{Vars}| \cdot |E_C|)^{O(\mathrm{Idx}(G_C))}$ distinct paths. Single-letter case (Section 6, Proposition 6.4): in the backward elimination of replaceAll terms each regular constraint collected on a variable descends from an original constraint along one path, so with bounded diamond index each variable collects polynomially many constraints and the procedure, which guesses its choices (such as the sets $T_z$ of state pairs) nondeterministically, runs in nondeterministic polynomial space, hence in polynomial space by Savitch's theorem. Constant-string case (Section 7 and Appendix D) and regular-expression case (Section 8 and Appendix E): each elimination step along an l-edge enlarges the automata through the parsing construction, so the bound on l-length controls the state count. Lower bound: nonemptiness of the intersection of regular expressions $e_1, \dots, e_n$ over $\{0, 1\}$ is PSPACE-complete and is the satisfiability of $x \in e_1 \wedge \dots \wedge x \in e_n$, which lies in every fragment. The expansion should reuse the pre-image constructions of the EXPSPACE procedure with these quantitative invariants, one page per pattern class if needed.

## Sources

- T. Chen, Y. Chen, M. Hague, A. W. Lin and Z. Wu, "What is decidable about string constraints with the ReplaceAll function", Proceedings of the ACM on Programming Languages 2 (POPL), Article 3, 2018, doi:[10.1145/3158091](https://doi.org/10.1145/3158091); full version arXiv:1711.03363v1, <https://arxiv.org/abs/1711.03363v1>: Proposition 3.6 and the paragraph after it (replaceAll-only formulas), Definitions 4.3–4.4, Proposition 4.5, Corollary 4.7 with the paragraph after it, Proposition 6.4 with its proof (Section 6.2.1), and Appendices D and E.
- T. Chen, M. Hague, A. W. Lin, P. Rümmer and Z. Wu, "Decision procedures for path feasibility of string-manipulating programs with complex operations", Proceedings of the ACM on Programming Languages 3 (POPL), Article 49, 2019, doi:[10.1145/3290362](https://doi.org/10.1145/3290362); full version arXiv:1811.03167v1, <https://arxiv.org/abs/1811.03167v1>: Appendix C, Example C.1 (layers of replaceAll and concatenation in the hardness construction).
