# Emptiness of distributed automata is undecidable, already on directed paths

No algorithm decides whether a given distributed automaton accepts some pointed directed path, and none decides whether it
accepts some pointed graph at all.

**Theorem.** For [distributed automata](distributed-automata.md), the directed-path emptiness problem is undecidable: given
$\mathcal{A}$, it is undecidable whether $\mathcal{A}$ accepts some pointed directed path. The general emptiness problem, whether
$\mathcal{A}$ accepts some pointed graph, is undecidable as well.

By contrast, emptiness is decidable for *forgetful* distributed automata, in which the next state of a node does not depend on its
own current state, and on directed paths forgetful automata are equivalent to finite word automata.

## Depends on

- [Distributed automata](distributed-automata.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof reduces the halting problem for deterministic one-tape Turing machines started on the empty tape. Since communication
along a directed path goes only one way, the tape cannot be laid out along the path; instead space and time are exchanged: the
$i$-th node of the path stays waiting for a number of rounds and then plays the role of a time step of the machine, its state
holding the contents of the currently visited cell, so that the run of the automaton along the path traces the computation. The
automaton accepts some pointed directed path exactly when the machine halts. For the general problem, make the automaton
*monovisioned*: it enters a rejecting sink whenever a node sees more than one state among its incoming neighbors or sees the
sink. Every nonempty language contains a pointed directed tree (by unraveling), and a monovisioned automaton accepting a tree
also accepts a directed path, so the two emptiness problems coincide for monovisioned automata.

## Sources

- A. Kuusisto and F. Reiter, "Emptiness problems for distributed automata", *Information and Computation* 272, article 104503, 2020, doi:10.1016/j.ic.2019.104503; conference version in *GandALF 2017*, Electronic Proceedings in Theoretical Computer Science 256, pp. 210–222, 2017, doi:10.4204/EPTCS.256.15. Section 5 of the version arXiv:1705.02609v2: Theorem 5 with its proof sketch, Lemmas 6 and 7 (tree model property and monovisioned automata), and Theorem 4 and Proposition 2 (forgetful automata).
