# Emptiness of quasi-acyclic distributed automata is undecidable

No algorithm decides whether a given quasi-acyclic distributed automaton, whose state diagram has no cycles except self-loops,
accepts some pointed graph.

**Theorem.** The emptiness problem for quasi-acyclic [distributed automata](distributed-automata.md) is undecidable: given a
quasi-acyclic automaton $\mathcal{A} = (Q, \iota, \delta, F)$ over $1$-relational graphs, the form in which quasi-acyclicity is defined, it is undecidable whether some pointed graph is accepted by $\mathcal{A}$.

The source notes that its proof for directed paths does not go through for quasi-acyclic automata, so this result needs a
different construction; it also gives a second proof that general emptiness is undecidable.

## Depends on

- [Distributed automata](distributed-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the Post correspondence problem over the alphabet $\{0, 1\}$, viewing the pairs of words as dominoes. The
distinguished node, the "spectator", has one incoming neighbor $v_j$ for each domino $i_j$ of a putative solution, and witnesses
simultaneous left-to-right traversals of the top word and the bottom word of the sequence, one bit per round, checking that they
match. Each $v_j$ must send the bits of its domino at the right times; this timing is achieved by attaching to $v_j$ a "fuse", a
tree-shaped gadget along which two signals travel at different speeds from time $0$ and trigger the firing of the top and the
bottom word. Quasi-acyclic automata are closed under union and intersection by a product construction, which is used to combine
the checks. The resulting automaton accepts some pointed graph exactly when the instance has a solution.

## Sources

- A. Kuusisto and F. Reiter, "Emptiness problems for distributed automata", *Information and Computation* 272, article 104503, 2020, doi:10.1016/j.ic.2019.104503; conference version in *GandALF 2017*, Electronic Proceedings in Theoretical Computer Science 256, pp. 210–222, 2017, doi:10.4204/EPTCS.256.15. Section 6 of the version arXiv:1705.02609v2: Theorem 9 with its proof sketch and Lemma 8 (closure under union and intersection).
