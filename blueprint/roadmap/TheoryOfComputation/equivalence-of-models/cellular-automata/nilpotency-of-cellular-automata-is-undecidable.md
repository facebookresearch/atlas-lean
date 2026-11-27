# Nilpotency of cellular automata is undecidable

For every $d \ge 1$ it is undecidable whether a given $d$-dimensional [cellular automaton](cellular-automata-on-z-d.md) is
nilpotent, that is, whether some power $G^n$ maps every configuration to the same configuration. For $d = 2$, a tile set
$T$ gives an automaton with states $T \cup \{q\}$ that keeps a tile where the tiling is valid and writes $q$ elsewhere; it is
nilpotent exactly when $T$ admits no valid tiling. For $d = 1$, an NW-deterministic tile set $T$ gives an automaton with
neighborhood $(0, 1)$ and states $T \cup \{q\}$ whose space–time diagrams without $q$ are the valid tilings by $T$.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)

## Proof depends on

- [The tiling problem is undecidable](../../undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)
- [The tiling problem for NW-deterministic tile sets is undecidable](../../undecidable-problems/wang-tiles/the-tiling-problem-for-nw-deterministic-tile-sets.md)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Section 2.4 (nilpotency), Theorem 15 (Culik, Pachl and Yu; Kari) and its proof in Section 7.
