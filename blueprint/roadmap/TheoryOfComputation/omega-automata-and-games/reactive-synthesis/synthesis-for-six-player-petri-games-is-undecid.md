# Synthesis for six-player Petri games with local safety is undecidable

No algorithm decides whether the system players of a Petri game with six players have a winning strategy for a local safety condition.

**Petri nets.** A *Petri net* $N = (\mathcal{P}, \mathcal{T}, \mathit{pre}, \mathit{post}, \mathit{In})$ has disjoint sets of places and transitions, maps $\mathit{pre}$ to nonempty finite sets of places and $\mathit{post}$ to finite sets of places, and an initial marking $\mathit{In}$. A transition $t$ is enabled at a marking $M$ if $\mathit{pre}(t) \subseteq M$, and firing it yields $M - \mathit{pre}(t) + \mathit{post}(t)$. The net is *safe* if every reachable marking puts at most one token on each place.

**Petri games.** A *Petri game* $G = (\mathcal{P}^S, \mathcal{P}^E, \mathcal{T}, \mathit{pre}, \mathit{post}, \mathit{In}, \mathcal{B})$ is a finite safe Petri net whose places are partitioned into *system places* $\mathcal{P}^S$ and *environment places* $\mathcal{P}^E$, together with a set $\mathcal{B}$ of *bad markings*. A token on a system place is a *system player*, a token on an environment place an *environment player*; tokens may move between the two kinds of places, and the number of players is the number of tokens. A *strategy* is a branching process $\sigma = (N, \pi)$ of the underlying net, a part of its unfolding, so each player decides on the basis of its whole causal history. It is *winning* if it satisfies:

- *justified refusal*: if a transition $t$ of $G$ is enabled by a set of pairwise concurrent places of $N$ but no copy of $t$ is kept on them, then some of these places is a system place from which $\sigma$ allows no copy of $t$;
- *safety*: no reachable marking of $N$ is mapped by $\pi$ to a bad marking;
- *determinism*: from a system place, at most one outgoing transition is enabled in each reachable marking;
- *deadlock avoidance*: in every reachable marking of $N$ some transition is enabled if one is enabled in its image under $\pi$.

The *synthesis problem* asks whether $G$ has a winning strategy. Under a *local safety condition* the bad markings are given by a set of bad places, a marking being bad when it covers one of them.

**Theorem (Hannibal).** The synthesis problem for Petri games with six players is undecidable, already when the winning condition is a local safety condition and the game has at most two system players at any time.

For comparison, the same paper shows that synthesis for two-player Petri games with a global safety condition is NP-complete and that it is decidable in nondeterministic exponential time for up to four players.

## Depends on

- [Place/transition Petri nets](../../../ComputerScience/concurrent-systems-and-protocols/petri-nets/place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction starts from the $\omega$ bipartite coloring problem, a variant of the tiling problem shown undecidable through the $\omega$ Post correspondence problem; a good expansion links pages for both problems. Theorem 4.1 of the source (Section 4) reduces the $\omega$ bipartite coloring problem to the synthesis problem for six-player Petri games with a global safety condition: players in a top and a bottom part of the net count rounds, after an environment player chooses a check transition a system player chooses a color, and bad markings forbid disallowed diagonal, vertical and horizontal patterns as well as inconsistent choices of the same color. The constructed game performs at most three checks along any sequence of transitions, so it has at most three system players at a time, and two concurrent checks already suffice; and adding a transition from each bad marking to a fresh bad place turns the global safety condition into a local one.

## Sources

- P. Hannibal, "(Un)Decidability Bounds of the Synthesis Problem for Petri Games", in *Proceedings of the 14th International Symposium on Games, Automata, Logics, and Formal Verification (GandALF 2023)*, Electronic Proceedings in Theoretical Computer Science 390, 2023, pp. 115–131, doi:10.4204/EPTCS.390.8; read as arXiv:2310.01000v1, <https://arxiv.org/abs/2310.01000v1>: Definitions 4.1 and 4.2 and Theorem 4.1 in Section 4 (the $\omega$ bipartite coloring problem reduces to synthesis for six-player Petri games) with the remarks after its proof (two system players, local safety), Theorem 3.4 (two to four players), the abstract and introduction (undecidability under local safety, the results for two and four players), and the definitions of Petri nets, Petri games and winning strategies in Section 2, in the numbering of that version.
