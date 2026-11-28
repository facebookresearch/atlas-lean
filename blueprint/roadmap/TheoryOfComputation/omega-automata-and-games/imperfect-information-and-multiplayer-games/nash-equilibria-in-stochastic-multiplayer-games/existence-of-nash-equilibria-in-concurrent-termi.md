# Existence of Nash equilibria in concurrent terminal-reward games is not recursively enumerable

The set of concurrent fourteen-player terminal-reward games that have a Nash equilibrium at all, with no constraint on the
payoff, is not recursively enumerable.

**Theorem.** The set of initialised concurrent $14$-player terminal-reward games $(\mathcal{G}, s_0)$, in the sense of
[concurrent limit-average games](concurrent-limit-average-games-and-their-nash-eq.md), that have a Nash equilibrium in
randomized strategies is not recursively enumerable. In particular, whether such a game has a Nash equilibrium is undecidable.

For turn-based games the question is trivial, since every turn-based game has a Nash equilibrium; the hardness of the plain
existence question comes from simultaneous moves.

## Depends on

- [Concurrent limit-average games and their Nash equilibria](concurrent-limit-average-games-and-their-nash-eq.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Constrained Nash equilibria in limit-average games are not recursively enumerable](constrained-nash-equilibria-in-limit-average-gam.md)

## Expansion

The proof removes the payoff constraint from the turn-based reduction. Take the disjoint union of the game $\mathcal{G}$ of that
reduction with a two-player concurrent terminal-reward game $\mathcal{G}_1$ that has no Nash equilibrium (a game of de Alfaro,
Henzinger and Kupferman), give player $0$ reward $0$ in every state of $\mathcal{G}_1$, and add a new initial state controlled by
player $0$, from which she moves either to the initial state of $\mathcal{G}$ or to that of $\mathcal{G}_1$. A Nash equilibrium of
the new game cannot enter $\mathcal{G}_1$, so it exists exactly when $(\mathcal{G}, s_0)$ has a Nash equilibrium in which player $0$
gets expected payoff at least $0$, that is, exactly when the simulated two-counter machine does not halt.

## Sources

- M. Ummels and D. Wojtczak, "The complexity of Nash equilibria in limit-average games", in *CONCUR 2011 – Concurrency Theory*, Lecture Notes in Computer Science 6901, pp. 482–496, Springer, 2011, doi:10.1007/978-3-642-23217-6_32; Section 7 of the version arXiv:1109.6220v1 (Corollary 26 and its proof, which refers to the proof of Corollary 10), and Section 3 (Example 1, the game without Nash equilibrium).
