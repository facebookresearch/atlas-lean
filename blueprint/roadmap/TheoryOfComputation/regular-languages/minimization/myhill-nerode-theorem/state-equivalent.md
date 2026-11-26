# Equivalent states of a DFA

Two states $p$ and $q$ of a DFA $M$ are equivalent when
they accept the same continuation language: for every word $z$, running $M$ from $p$ on $z$
ends in an accepting state if and only if running $M$ from $q$ on $z$ does.
