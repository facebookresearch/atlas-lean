# Regularity of the continuity set of an ω-rational function is Π¹₁-complete

Deciding whether the continuity set of an ω-rational function, given by a functional Büchi transducer, is a regular
ω-language is $\Pi^1_1$-complete.

**Theorem.** The set of (codes of) Büchi transducers $\mathcal{T}_z$ with a functional relation such that the continuity set
$C(F_{\mathcal{T}_z})$, in the sense of [infinitary rational relations](infinitary-rational-relations-and-omega-rational.md), is a regular ω-language is [$\Pi^1_1$-complete](../../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md).

Undecidability of this problem, and of the analogous question for context-free ω-languages, was proved earlier by Carton,
Finkel and Simonnet. For context-free ω-languages the source shows that the set is $\Pi^1_1$-hard and lies in
$\Pi^1_2 \setminus \Sigma^1_1$, without determining its exact level.

## Depends on

- [Infinitary rational relations and ω-rational functions](infinitary-rational-relations-and-omega-rational.md)
- [Analytical hierarchy](../../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)

## Proof depends on

- [The infinite PCP in a regular ω-language is Σ¹₁-complete](../../../../undecidable-problems/post-correspondence-problem/infinite-pcp-in-a-regular-omega-language-is.md)

## Expansion

*Membership.* $C(F_{\mathcal{T}_z})$ is regular iff some Büchi automaton $\mathcal{A}_{z'}$ satisfies
$\forall x\, [x \in C(F_{\mathcal{T}_z}) \leftrightarrow x \in L(\mathcal{A}_{z'})]$; with the arithmetical description of
continuity points and of membership in a regular ω-language this is a $\Pi^1_1$ condition after an existential number
quantifier, hence $\Pi^1_1$. *Hardness* reduces the infinite PCP in a regular ω-language to non-regularity of the continuity set, adapting a construction
of Carton, Finkel and Simonnet. The function prefixes the construction for continuity points with a block over three new
letters that drives the fixed instance $((c^2, d, d), (c, c, d^2))$ of the Post correspondence problem, whose solutions
$\{1^i 2^i 3^i\} \cup \{3^i 2^i 1^i\}$ ($i \ge 1$) form a language that is not context-free; the continuity set fails to be
regular exactly when the given instance has a solution.

## Sources

- O. Finkel, "Three applications to rational relations of the high undecidability of the infinite Post correspondence problem in a regular ω-language", *International Journal of Foundations of Computer Science* 23(7):1481–1497, 2012, doi:[10.1142/S0129054112400606](https://doi.org/10.1142/S0129054112400606). Numbering of the version read, arXiv:1107.5886v1: Theorem 4.9, Lemma 4.10, Theorem 4.8 (Carton, Finkel and Simonnet) and Theorem 4.11 (the context-free case).
