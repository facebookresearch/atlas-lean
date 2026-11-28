# Inclusion and equivalence of real-time Büchi one-counter automata are Π¹₂-complete

Whether the $\omega$-language of one real-time Büchi one-counter automaton is included in, or equal to, that of another is $\Pi^1_2$-complete.

**Theorem.** For [real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md) over $\Omega$:
1. $\{(y,z)\in\mathbb N^2: L(\mathcal C_y)\subseteq L(\mathcal C_z)\}$ is $\Pi^1_2$-complete;
2. $\{(y,z)\in\mathbb N^2: L(\mathcal C_y)=L(\mathcal C_z)\}$ is $\Pi^1_2$-complete.

Subsets of $\mathbb N^2$ are identified with subsets of $\mathbb N$ through a computable pairing function, so the classes and reductions of the analytical hierarchy apply to them.

Both problems are also $\Pi^1_2$-complete for Büchi pushdown automata (Corollary 3.16 of the source).

## Depends on

- [Real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md)
- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)

## Proof depends on

- [Universality of real-time Büchi one-counter automata is Π¹₂-complete](universality-of-one-counter-omega-languages.md)

## Expansion

Membership: inclusion says that for all $\sigma$ and all runs $r$ there is a run $r'$ such that if $r$ accepts $\sigma$ for $\mathcal C_y$ then $r'$ accepts it for $\mathcal C_z$, a $\Pi^1_2$ formula; equivalence is the conjunction of two inclusions. Hardness: with $n_0$ an index of an automaton accepting $\Omega^\omega$, universality of $\mathcal C_z$ is $L(\mathcal C_{n_0})\subseteq L(\mathcal C_z)$, and also $L(\mathcal C_{n_0})=L(\mathcal C_z)$, so the $\Pi^1_2$-complete universality problem reduces to both.

## Sources

- Olivier Finkel, "Highly Undecidable Problems For Infinite Computations", *RAIRO - Theoretical Informatics and Applications* 43(2), 2009, pp. 339–364, doi:[10.1051/ita/2009001](https://doi.org/10.1051/ita/2009001); read in arXiv:0901.0373v1 ([arXiv](https://arxiv.org/abs/0901.0373v1)), whose numbering is used: Theorem 3.15 and its proof; Corollary 3.16.
