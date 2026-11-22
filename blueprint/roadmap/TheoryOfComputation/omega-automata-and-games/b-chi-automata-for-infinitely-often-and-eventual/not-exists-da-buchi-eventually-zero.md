# No deterministic Büchi automaton accepts "eventually always 0"

No deterministic Büchi automaton over the alphabet $\{0, 1\}$, with any set of states, finite
or infinite, accepts exactly the infinite words that are eventually constantly $0$.

Vardi's Proposition 8 states this for $(0 + 1)^* 1^\omega$, the same language with the two
letters exchanged. His proof builds, from a hypothetical deterministic automaton, a word with
infinitely many $0$s whose run visits accepting states infinitely often. Another proof:
the language of a deterministic Büchi automaton is the ω-limit of the language of finite words
accepted by the same automaton, and "eventually always $0$" is not the ω-limit of any language
of finite words.

## Background

- [Eventually always](eventually-always.md): the language for $p = \{0\}$.

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 2.2, Proposition 8.
