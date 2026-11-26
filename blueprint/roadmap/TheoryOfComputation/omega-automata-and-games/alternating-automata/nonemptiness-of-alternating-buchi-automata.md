# Nonemptiness of alternating Büchi automata is PSPACE-complete

Deciding whether an [alternating Büchi automaton](alternating-buchi-automata.md) accepts some infinite word is PSPACE-complete, and it is decidable
in exponential time. Membership follows from the Miyano–Hayashi translation and the emptiness test for Büchi automata; hardness, by a synchronized
reduction from the nonemptiness of alternating automata on finite words: add a fresh end letter on which exactly the accepting states move
to $\mathrm{true}$ and the others to $\mathrm{false}$, keep all other transitions, and use no Büchi accepting state; then every branch must reach the end
letter at the same position, so the new automaton accepts some infinite word exactly when the given automaton accepts some finite word.

## Depends on

- [Alternating Büchi automata](alternating-buchi-automata.md)

## Proof depends on

- [Miyano–Hayashi theorem](miyano-hayashi-theorem.md)
- [Nonemptiness of alternating automata is PSPACE-complete](nonemptiness-of-alternating-automata-is-pspace-complete.md)
- [Lasso characterization of Büchi nonemptiness](../emptiness-of-b-chi-automata/language-nonempty-iff-has-lasso.md)

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Proposition 21 and its proof, with Propositions 13 and 20.
