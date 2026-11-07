# Rabin-to-Muller conversion preserves the language

If the state space is finite, then a
Rabin automaton $r$ accepts the same language as its Muller presentation: the Muller automaton
with the same transitions and initial states as $r$ whose acceptance sets are the sets $S$ of
states such that, for some Rabin pair $(E, F)$ of $r$, $S$ meets $E$ and is disjoint from $F$.
