# Universality of unranked tree automata with sibling constraints is undecidable

For nondeterministic bottom-up automata on unranked trees whose transitions may test equality or disequality of direct subtrees, emptiness is decidable but universality is undecidable.

Unranked trees are finite trees over a finite alphabet $\Sigma$ in which a node may have any finite number of ordered children. An *atomic sibling constraint* over a state set $Q$ is given by an MSO formula $\varphi(x,y)$ over words over $Q$ and has one of the forms $\forall x\forall y\,(\varphi\to t_x=t_y)$, $\exists x\exists y\,(\varphi\wedge t_x=t_y)$, $\forall x\forall y\,(\varphi\to t_x\ne t_y)$ or $\exists x\exists y\,(\varphi\wedge t_x\ne t_y)$, where $t_x$ is the subtree at the $x$-th child; a *sibling constraint* is a positive Boolean combination of atomic ones. A *UTACS* $(Q,\Sigma,\Lambda,\Delta,F)$ extends a nondeterministic bottom-up [tree automaton](../../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md) to unranked trees: leaf transitions $\Lambda\subseteq\Sigma\times Q$ and inner transitions $(L,\alpha,a,q)$ with a regular language $L\subseteq Q^+$ and a sibling constraint $\alpha$, applicable at an $a$-labeled node whose children's states form a word of $L$ that, together with the children's subtrees, satisfies $\alpha$. A tree is accepted if some run reaches a final state at the root.

**Theorem (Löding and Wong).** The universality problem for nondeterministic UTACS, whether every unranked tree is accepted, is undecidable (Theorem 8).

By contrast, the emptiness problem for nondeterministic UTACS is decidable (Theorem 1). For deterministic UTACS universality is decidable, since they are effectively closed under complement. As a consequence, for a fragment of MSO over data words with restricted data comparisons, satisfiability is decidable but validity is undecidable.

## Depends on

- [Bottom-up finite tree automata](../../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md)
- [Monadic second-order logic over words](../../../omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for two-register (two-counter) machines: a computation is written as a word $p_1\perp a^{d_1}\perp b^{e_1}\#\cdots\#p_m\perp a^{d_m}\perp b^{e_m}$, with $\#$ separating configurations, each symbol becoming the root of a unary tree, all attached to one root, so that the unary trees act as data values. A UTACS accepts every tree that is not the encoding of a halting computation, so it is universal iff the machine does not halt; equality and disequality of sibling subtrees check that consecutive configurations are related correctly, with extra requirements on the unary trees replacing a $\forall x\exists y$ constraint that UTACS cannot express.

## Sources

- Christof Löding and Karianto Wong, "On Nondeterministic Unranked Tree Automata with Sibling Constraints", in *IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2009)*, LIPIcs 4, 2009, pp. 311–322, doi:[10.4230/LIPIcs.FSTTCS.2009.2328](https://doi.org/10.4230/LIPIcs.FSTTCS.2009.2328); read in the open-access LIPIcs copy at https://drops.dagstuhl.de/opus/volltexte/2009/2328/: Section 2 (sibling constraints and UTACS), Theorem 1, Theorem 8 with its proof sketch in Section 4, and Section 5.
