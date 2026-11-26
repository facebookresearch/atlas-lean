# Nondeterministic Büchi automata are strictly more expressive than deterministic ones

Every deterministic Büchi automaton over $\{0, 1\}$ can be read as a nondeterministic one with
the same states and language.
Conversely, the ω-language of the infinite words over $\{0, 1\}$ that are eventually constantly
$0$ is accepted by a nondeterministic Büchi automaton with two states, which guesses the point
after which only $0$ occurs, but by no deterministic Büchi automaton.

Unlike automata on finite words, Büchi automata cannot be determinized. This is why
complementation of Büchi automata cannot proceed by the subset construction, and why LTL is
translated to nondeterministic automata.

## Informally uses

- [No deterministic Büchi automaton accepts "eventually always 0"](not-exists-da-buchi-eventually-zero.md):
  the negative half.

## Background

- [Two-state Büchi automaton for “eventually always”](eventually-always-na.md): the same
  guessing automaton, for an arbitrary set $p$ of letters.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.2, Proposition 8 and the automaton $A_0$ before it.
