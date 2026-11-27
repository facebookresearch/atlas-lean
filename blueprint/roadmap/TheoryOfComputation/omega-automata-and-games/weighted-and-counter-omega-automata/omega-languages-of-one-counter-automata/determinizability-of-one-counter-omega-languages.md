# Complementability and determinizability of real-time Büchi one-counter automata are Π¹₂-complete

Whether the complement of the $\omega$-language of a real-time Büchi one-counter automaton is accepted by such an automaton, and whether the language is accepted by a deterministic one, are both $\Pi^1_2$-complete.

**Theorem.** For [real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md) over $\Omega$:
1. (complementability) $\{z: \exists y\ \Omega^\omega\setminus L(\mathcal C_z)=L(\mathcal C_y)\}$ is $\Pi^1_2$-complete;
2. (determinizability) $\{z: \exists y\in D_C\ L(\mathcal C_z)=L(\mathcal C_y)\}$ is $\Pi^1_2$-complete, where $D_C$ is the recursive set of indices of deterministic real-time Büchi one-counter automata.

Both problems are also $\Pi^1_2$-complete for Büchi pushdown automata (Corollary 3.20 of the source).

## Depends on

- [Real-time Büchi one-counter automata](real-time-buchi-one-counter-automata.md)
- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)

## Proof depends on

None.

## Expansion

Membership: each property is a number quantifier over indices $y$ in front of a $\Pi^1_2$ equality of $\omega$-languages. Hardness uses the reduction $H\circ\varphi$ of the regularity proof: in the first case the automaton accepts $\Omega^\omega$, which is deterministic and has empty, hence accepted, complement; in the second case its complement is accepted by no Turing machine, so by no one-counter automaton, and the language is not deterministic, since a deterministic one would lie in the arithmetical class $\Pi_2$ and have a complement accepted by a Turing machine.

## Sources

- Olivier Finkel, "Highly Undecidable Problems For Infinite Computations", *RAIRO - Theoretical Informatics and Applications* 43(2), 2009, pp. 339–364, doi:[10.1051/ita/2009001](https://doi.org/10.1051/ita/2009001); read in arXiv:0901.0373v1 ([arXiv](https://arxiv.org/abs/0901.0373v1)), whose numbering is used: Theorem 3.19 and its proof; Corollary 3.20.
