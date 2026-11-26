# Nonemptiness of alternating automata is PSPACE-complete

Deciding whether an [alternating automaton](alternating-automata-on-finite-words.md) on finite words accepts some word is PSPACE-complete, and
it is decidable in exponential time through the translation to nondeterministic automata. Hardness follows from the PSPACE-hardness of
universality for nondeterministic automata, since such an automaton is an alternating one whose dual accepts the complement.

## Depends on

- [Alternating automata on finite words](alternating-automata-on-finite-words.md)

## Proof depends on

- [Alternating automata recognize exactly the regular languages](alternating-automata-recognize-exactly-the-regular.md)
- [Complementing alternating automata by dualization](complementing-alternating-automata-by-dualization.md)

## Expansion

This page becomes ready once:

- PSPACE-completeness of the nonuniversality problem for nondeterministic finite automata (Meyer and Stockmeyer) (proof prerequisite; not yet stated)

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Proposition 18 and its proof, with Propositions 11 and 12.
