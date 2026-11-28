# Existence of a continuity point of an ω-rational function is Σ¹₁-complete

Deciding whether an ω-rational function, given by a functional Büchi transducer, has at least one point of continuity is
$\Sigma^1_1$-complete, although continuity everywhere is decidable.

**Theorem.** The set of (codes of) Büchi transducers $\mathcal{T}_z$ with a functional relation such that the continuity set
$C(F_{\mathcal{T}_z})$ is nonempty, in the sense of [infinitary rational relations](infinitary-rational-relations-and-omega-rational.md), is [$\Sigma^1_1$-complete](../../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md).

Undecidability of this problem was proved earlier by Carton, Finkel and Simonnet; the theorem gives its exact complexity. By
contrast, whether an ω-rational function is continuous (on its whole domain) is decidable (Prieur).

## Depends on

- [Infinitary rational relations and ω-rational functions](infinitary-rational-relations-and-omega-rational.md)
- [Analytical hierarchy](../../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The infinite PCP in a regular ω-language is Σ¹₁-complete](../../../../undecidable-problems/post-correspondence-problem/infinite-pcp-in-a-regular-omega-language-is.md)

## Expansion

*Membership.* For $X_{k,n} = \{x \in \mathrm{Dom}(F) \mid \forall y \in \mathrm{Dom}(F)\ [d(x, y) < 2^{-k} \Rightarrow d(F(x), F(y)) < 2^{-n}]\}$,
a point $x$ is in $C(F)$ iff $\forall n\, \exists k\ x \in X_{k,n}$. Whether $F$ maps the cylinder of $x$'s first $k + 1$ letters,
intersected with the domain, into a single cylinder of length $n + 1$ is decidable from $x$'s prefix with Büchi automata, and
membership in the regular domain is arithmetical, so $C(F) \ne \emptyset$ is an existential function quantifier over an
arithmetical formula. *Hardness* reduces the infinite PCP in a regular ω-language, adapting a construction of Carton, Finkel
and Simonnet: the function is built over the alphabet $\{1, \dots, n, a, b\}$ so that its continuity points correspond to
solutions of the instance.

## Sources

- O. Finkel, "Three applications to rational relations of the high undecidability of the infinite Post correspondence problem in a regular ω-language", *International Journal of Foundations of Computer Science* 23(7):1481–1497, 2012, doi:[10.1142/S0129054112400606](https://doi.org/10.1142/S0129054112400606). Numbering of the version read, arXiv:1107.5886v1: Theorem 4.6, Lemma 4.7, Theorem 4.4 (Prieur) and Theorem 4.5 (Carton, Finkel and Simonnet).
