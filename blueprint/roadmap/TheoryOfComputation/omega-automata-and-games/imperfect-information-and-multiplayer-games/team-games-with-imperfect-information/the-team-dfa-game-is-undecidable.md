# The team DFA game is undecidable

No algorithm decides whether the two-player team has a forced win in a given team DFA game, where an all-seeing adversary and two
team members who see only part of the adversary's moves feed bits to a finite automaton.

**Theorem (Coulombe and Lynch, 2018; journal version *Theoretical Computer Science* 839, 2020; as restated in the source).** Given an instance $D$ of the [team DFA game](the-team-dfa-game-and-its-communication-variant.md), it is undecidable
whether the existential team has a forced win.

The game has a bounded state space, a finite automaton, so the undecidability comes from the imperfect information of the team
members, not from unbounded memory in the game.

## Depends on

- [The team DFA game and its communication variant](the-team-dfa-game-and-its-communication-variant.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The team DFA game was introduced by Coulombe and Lynch as a bounded-state simplification of the team computation game, a team game
of private information whose undecidability goes back to Peterson and Reif's work on multiple-person alternation. The later source
recalls the result as a theorem and uses it as the starting point of its reductions; it does not reproduce the proof.

## Sources

- M. Coulombe and J. Lynch, "Characterizing the decidability of finite state automata team games with communication", in *GandALF 2022*, Electronic Proceedings in Theoretical Computer Science 370, pp. 213–228, 2022, doi:10.4204/EPTCS.370.14; read in arXiv:2209.10324v1: Theorem 1 in Section 1.1, stating that the team DFA game is undecidable, credited to the paper above.
