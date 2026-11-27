# Negated string containment is decidable

Whether some assignment of words from given regular languages to variables makes a term $N$ not occur as a factor of a term $H$ is decidable in EXPSPACE, and NP-hard; the source gives no matching bound.

Fix a finite alphabet $\Sigma$ and a finite set $X$ of string variables. A *term* is a word over $X \cup \Sigma$. A *negated containment constraint* is

$$
\varphi = \neg\mathrm{Contains}(N, H) \wedge \bigwedge_{x \in X} x \in L_x,
$$

with terms $N$ (the needle) and $H$ (the haystack) and, for each variable, a regular language $L_x$ given by a nondeterministic finite automaton. An assignment $\sigma : X \to \Sigma^*$, extended to terms by $\sigma(a) = a$ for letters and by concatenation, satisfies $\varphi$ if $\sigma(x) \in L_x$ for every $x$ and $\sigma(N)$ is not a factor of $\sigma(H)$, that is, $\sigma(H) \neq u \, \sigma(N) \, v$ for all words $u, v$. Since the empty word is a factor of every word, $\varphi$ is unsatisfiable whenever $\sigma(N)$ must be empty.

1. Satisfiability of negated containment constraints is decidable in [EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md).
2. It is NP-hard.

The result covers exactly one negated containment together with regular memberships. The source lists as open the extension to several negated containments and the combination with length constraints or disequalities; it also states, as a consequence, decidability when a conjunction of chain-free word equations is added, through a monadic decomposition of such equations, which is not included here. The positive predicate $\mathrm{Contains}(N, H)$ is the word equation $H = u N v$ with fresh $u, v$; its negation is not of that form.

## Depends on

- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Cooper's theorem](../presburger-arithmetic-and-real-addition/cooper-s-theorem.md)

## Expansion

This node still needs its proof broken down; the source proof has these parts.

A language is *flat* if it is a finite union of sets $w_1 w_2^* w_3 w_4^* \cdots w_{\ell - 1}^* w_\ell$; a regular language is non-flat exactly when it contains some $p \{u, v\}^* s$ with $u, v$ not powers of a common word (Fact 1). Normalization (Lemma 3): a constraint is transformed into the formula true or into a disjunction of normalized constraints, in which no variable has a finite language and every variable is decomposed: its language is given by a deterministic automaton with a single initial state, a single final state and exactly one nontrivial maximal strongly connected component, and no other strongly connected components. Flat case (Lemma 4, from Chen, Havlena, Hečko, Holík and Lengál, PLDI 2025): if all languages are flat, the constraint reduces, through Parikh images of runs of the automata, to a Presburger arithmetic formula, which must also express the universally quantified condition that no position of the haystack starts an occurrence of the needle (PLDI 2025, Section 6.4); the source states a NEXPTIME bound. Two-sided non-flat variables (Theorem 11, Section 4): a non-flat variable occurring in both $N$ and $H$ can be replaced by a fresh letter $\#$ without changing satisfiability, because its language contains long words built from fresh primitive words of distinct lengths whose occurrences cannot overlap without a conflict (Fine and Wilf; Lyndon–Schützenberger, Lemmas 5–9 and Corollaries 7 and 10). One-sided non-flat variables (Theorem 22, Section 6): a non-flat variable occurring only in $H$ can, after enumerating its short assignments up to computable bounds, be replaced by a flat language preserving satisfiability, and a model is glued back (Lemmas 16–17, 25). Algorithm 1 combines these steps; it is sound and complete (Theorems 26–27) and runs in exponential space (Theorem 28), the space needed to write the model of the two-sided variables. NP-hardness (Theorem 2) is cited from the PLDI 2025 paper: technical report arXiv:2504.07033v1, Theorem 7.5 and Appendix D.

## Sources

- V. Havlena, M. Hečko, L. Holík and O. Lengál, "Negated string containment is decidable", 50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025), LIPIcs 345, Article 56, 2025, doi:[10.4230/LIPIcs.MFCS.2025.56](https://doi.org/10.4230/LIPIcs.MFCS.2025.56); technical report arXiv:2506.22061v2, <https://arxiv.org/abs/2506.22061v2>: numbering of the published version, Section 2 (flat languages, Fact 1, the constraint, Theorem 2), Section 2.1 (Lemmas 3–4), Section 4 (Theorem 11), Section 6 (Theorem 22), Section 7 (Algorithm 1, Theorems 26–28), Section 7.1 (Theorem 29) and Section 8.
- Y.-F. Chen, V. Havlena, M. Hečko, L. Holík and O. Lengál, "A uniform framework for handling position constraints in string solving", Proceedings of the ACM on Programming Languages 9 (PLDI), 2025, doi:[10.1145/3729273](https://doi.org/10.1145/3729273); technical report arXiv:2504.07033v1, <https://arxiv.org/abs/2504.07033v1>: Section 6.4 (the flat-language procedure for negated containment), Theorem 7.5 and Appendix D (NP-hardness of a single negated containment), cited by the MFCS 2025 paper as reference [19].
