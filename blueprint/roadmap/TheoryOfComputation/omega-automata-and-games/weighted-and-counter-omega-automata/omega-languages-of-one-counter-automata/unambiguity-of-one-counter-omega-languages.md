# Unambiguity of real-time Büchi one-counter ω-languages is Π¹₂-complete

Whether the $\omega$-language of a real-time Büchi one-counter automaton is accepted by some unambiguous such automaton is $\Pi^1_2$-complete.

**Theorem.** The unambiguity problem for [real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md) over $\Omega$ is $\Pi^1_2$-complete: the set of $z$ such that $L(\mathcal C_z)=L(\mathcal C_y)$ for some $\mathcal C_y$ having at most one accepting run on each infinite word is $\Pi^1_2$-complete.

The same holds for context-free $\omega$-languages given by Büchi pushdown automata (Corollary 3.22 of the source).

## Depends on

- [Real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md)
- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)

## Proof depends on

None.

## Expansion

Membership: that an automaton is unambiguous is a $\Pi^1_1$ statement (any two accepting runs on the same word are equal), and the property is a number quantifier over $y$ in front of it and a $\Pi^1_2$ equivalence. Hardness reduces universality of Turing machines on infinite words. Fix a $\boldsymbol\Sigma^1_1$-complete $\omega$-language $L$ accepted by a one-counter automaton, and let $\theta(z)$ index a machine accepting $(L\otimes\Sigma^\omega)\cup(\Sigma^\omega\otimes L(\mathcal M_z))$, where $\otimes$ interleaves two words. If $L(\mathcal M_z)=\Sigma^\omega$, the automaton $\mathcal C_{H(\theta(z))}$ accepts $\Omega^\omega$, unambiguously. Otherwise a section of the language is $L$, so the language is not Borel, and this survives the codings; by a result of Finkel and Simonnet a non-Borel context-free $\omega$-language is inherently ambiguous.

## Sources

- Olivier Finkel, "Highly Undecidable Problems For Infinite Computations", *RAIRO - Theoretical Informatics and Applications* 43(2), 2009, pp. 339–364, doi:[10.1051/ita/2009001](https://doi.org/10.1051/ita/2009001); read in arXiv:0901.0373v1 ([arXiv](https://arxiv.org/abs/0901.0373v1)), whose numbering is used: Theorem 3.21 and its proof; Corollary 3.22.
