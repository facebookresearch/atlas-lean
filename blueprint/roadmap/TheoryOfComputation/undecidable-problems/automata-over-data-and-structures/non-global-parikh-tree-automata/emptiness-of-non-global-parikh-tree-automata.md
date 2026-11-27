# Emptiness of non-global Parikh tree automata with three counters is undecidable

Tree automata that add counter vectors along each path and test, at every leaf, whether the vector reached lies in a semilinear set have an undecidable emptiness problem as soon as they have three counters.

**Theorem.** Let $m \ge 1$. A (non-global) *Parikh tree automaton of dimension $m$* ($m$-PTA) is a tuple $\mathcal A = (Q, \Sigma, q_0, \Delta, C)$ where $Q$ is a finite set of states, $\Sigma$ a ranked alphabet, $q_0 \in Q$ the initial state, $C \subseteq \mathbb N^m$ a [semilinear set](../../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md), and $\Delta$ a finite set of transitions $q \to \sigma(q_1(d_1), \ldots, q_n(d_n))$ with $\sigma \in \Sigma$ of rank $n$, $q, q_1, \ldots, q_n \in Q$ and $d_1, \ldots, d_n \in \mathbb N^m$. A computation starts from the configuration $(q_0, \mathbf 0)$ at the root; a configuration $(q, w)$ at a node may be rewritten by a transition $q \to \sigma(q_1(d_1), \ldots, q_n(d_n))$ with $n \ge 1$ into the symbol $\sigma$ with children in configurations $(q_1, w + d_1), \ldots, (q_n, w + d_n)$, and by a transition $q \to \alpha$ with $\alpha$ of rank $0$ into the leaf $\alpha$ only if $w \in C$. The language $L(\mathcal A)$ is the set of trees over $\Sigma$ produced by a computation from $(q_0, \mathbf 0)$. For every $m \ge 3$ there is no algorithm that decides, given an $m$-PTA $\mathcal A$, whether $L(\mathcal A) \neq \emptyset$.

Membership of a given tree is decidable even with a reset operation that sets a child's counters back to $\mathbf 0$ (Theorem 4 of the source), and emptiness is decidable for *linear* automata with resets, in which every transition resets the counters of all children but at most one (Theorem 3).

## Depends on

- [Semilinear set](../../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)
- [Bottom-up finite tree automata](../../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the reachability of a final state with both counters zero in a two-counter machine. Since a PTA cannot decrement, a counter vector $(s_1, s_2, l)$ represents the machine counters $(s_1 - l, s_2 - l)$, and $C = \{(i, i, i) : i \in \mathbb N\}$. Increments of counter $1$ or $2$ add $(2, 1, 1)$ or $(1, 2, 1)$. A decrement of counter $i$ adds $(0, 1, 1)$ or $(1, 0, 1)$ and branches: the right child continues the simulation, and the left child enters a checking state whose unary chain can reach an accepting leaf only if counter $i$ was positive. A zero test branches the same way, with a left child that can reach an accepting leaf only if counter $i$ is $0$. Final states produce a leaf, which requires the vector to lie in $C$, that is, both counters to be zero. So the automaton accepts some tree iff the machine reaches a final state with both counters zero.

## Sources

- L. Herrmann and J. Osterholzer, "Non-Global Parikh Tree Automata", in *Proceedings of the International Symposium on Games, Automata, Logics, and Formal Verification (GandALF 2024)*, Electronic Proceedings in Theoretical Computer Science 407, 2024, pp. 100–117, doi:[10.4204/EPTCS.407.8](https://doi.org/10.4204/EPTCS.407.8); read as arXiv:2409.06973v1, whose numbering is used here: Section 4 (definition of $m$-PTAR, Section 4.1 for $m$-PTA and linearity), Lemma 9, Theorem 2 with its proof, Theorem 3 and Theorem 4.
