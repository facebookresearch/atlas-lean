# Transition graph of a Büchi automaton

Let a Büchi automaton have a finite alphabet, a state type with decidable equality, a Boolean equality test agreeing with equality and a hash function, and decidable transitions, and let a duplicate-free list enumerate all its states. Its transition graph is the directed graph on the enumerated states in which the successors of $s$ are the enumerated states $t$ such that some letter takes $s$ to $t$, in enumeration order. The letters are forgotten: the graph records only whether some letter leads from one state to another.
