# Goal-state reachability for quantum observable MDPs is undecidable

No algorithm decides whether an agent controlling a quantum system by measurement operations, and observing their outcomes, can reach a goal quantum state with probability one in finitely many steps, although the analogous problem for classical partially observable MDPs is decidable.

A *quantum observable Markov decision process* (QOMDP) has a finite-dimensional Hilbert space whose states are density matrices $\rho$, a set $\Omega$ of observations and a finite set of actions, each a superoperator $A^a=\{A^a_1,\dots,A^a_{|\Omega|}\}$ given by Kraus matrices; taking action $a$ in state $\rho$ returns observation $o_i$ with probability $\mathrm{Tr}(A^a_i\rho A^{a\dagger}_i)$ and moves to $A^a_i\rho A^{a\dagger}_i/\mathrm{Tr}(A^a_i\rho A^{a\dagger}_i)$. A *goal QOMDP* adds an initial state $\rho_0$ and an absorbing goal state $\rho_g$. The *goal-state reachability problem* asks whether some policy, choosing actions from the observed history, reaches the goal state from the start in a finite number of steps with probability $1$. The source does not fix an encoding of the matrices; it reduces the quantum measurement occurrence problem (Theorem 2 of the source, after Eisert, Müller and Gogolin, by reduction from matrix mortality), whose instances are finite sets of Kraus matrices, so the problem is to be read for matrices with entries in a computable field such as the algebraic numbers.

**Theorem (Barry, Barry and Aaronson).** The goal-state reachability problem for goal QOMDPs is undecidable (Theorem 10 of arXiv:1406.2858v2).

By contrast, the goal-state reachability problem for goal POMDPs (classical partially observable MDPs) is decidable (Theorem 14 of arXiv:1406.2858v2).

Since QOMDPs contain POMDPs, the policy existence problem with infinite horizon is undecidable for QOMDPs as for POMDPs (Madani, Hanks and Condon), and with polynomial horizon it is PSPACE-complete for both.

## Depends on

- [Finite POMDPs](../../../../../../ComputerScience/heuristic-search-and-planning/partially-observable-planning/finite-pomdps.md)
- [Decidability by multi-stack machines](../../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from the *quantum measurement occurrence problem* of Eisert, Müller and Gogolin: given Kraus operators $K_1,\dots,K_{\mathcal K}$ of a superoperator, is there a finite sequence $i_1,\dots,i_n$ with $K_{i_1}^\dagger\cdots K_{i_n}^\dagger K_{i_n}\cdots K_{i_1}=0$, i.e. a sequence of outcomes that can never occur, even from a full-rank state. This problem is undecidable by reduction from matrix mortality (Theorem 2 of the source, citing Eisert, Müller and Gogolin). From an instance the source builds a goal QOMDP in which the agent can force the goal with probability $1$ iff some outcome sequence never occurs. For POMDPs, goal-state reachability reduces to reachability in a finite MDP over supports of belief states, which can be checked over finitely many stationary policies.

A good expansion links the undecidability of the quantum measurement occurrence problem.

## Sources

- Jennifer Barry, Daniel T. Barry and Scott Aaronson, "Quantum partially observable Markov decision processes", *Physical Review A* 90(3), 2014, article 032311, doi:[10.1103/PhysRevA.90.032311](https://doi.org/10.1103/PhysRevA.90.032311); read in arXiv:1406.2858v2 ([arXiv](https://arxiv.org/abs/1406.2858v2)), whose numbering is used: Definitions 1–5 (policy existence, goal-state reachability, QOMDPs, the quantum measurement occurrence problem and its goal QOMDP), Theorems 1 and 2, Theorem 10 with Lemmas 3–9, and Theorem 14.
