# Alternating automata recognize exactly the regular languages

For every nondeterministic finite automaton there is an [alternating automaton](alternating-automata-on-finite-words.md) of essentially the
same size with the same language, and for every alternating automaton with state set $S$ there is a nondeterministic finite automaton with
state set $2^S$ and the same language, which keeps a whole level of a run tree in its state (Brzozowski and Leiss; Chandra, Kozen and
Stockmeyer). Hence alternating automata on finite words recognize exactly the regular languages.

## Depends on

- [Alternating automata on finite words](alternating-automata-on-finite-words.md)

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Propositions 15 and 16 with their proofs.
