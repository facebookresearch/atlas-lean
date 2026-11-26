# Miyano–Hayashi theorem

For every [alternating Büchi automaton](alternating-buchi-automata.md) $\mathcal{A}$ with state set $S$ there is a nondeterministic
[Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) with state set $2^S \times 2^S$ accepting the same infinite words (Miyano and Hayashi). It guesses a run of $\mathcal{A}$ level by
level; a state $(U, V)$ records in $U$ the states of the current level whose branches still owe a visit to $F$ and in $V$ the others, and the
accepting states are those with $U = \emptyset$, the set $\{\emptyset\} \times 2^S$. Hence alternating Büchi automata recognize exactly the languages of Büchi automata, with an exponential translation, and
they are closed under complementation.

## Depends on

- [Alternating Büchi automata](alternating-buchi-automata.md)
- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Proof depends on

- [Büchi automata are closed under complementation](../boolean-closure-of-b-chi-automata/exists-buchi-compl.md)

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Proposition 20 (Miyano and Hayashi) with its construction, and the discussion after it on complementation via Propositions 7 and 19.
