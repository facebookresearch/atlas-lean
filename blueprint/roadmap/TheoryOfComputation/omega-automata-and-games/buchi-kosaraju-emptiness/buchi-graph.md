# Transition graph of a Büchi automaton

Let a Büchi automaton have a finite alphabet, a state type with decidable equality and a Boolean
equality test `==` that agrees with equality and a hash function, and decidable transitions; let a
duplicate-free list enumerate all its states. Its transition graph is the directed graph on the
enumerated states in which the successors of a state $s$ are the enumerated states $t$ such that
some letter takes $s$ to $t$, listed in enumeration order. The letters are forgotten.
