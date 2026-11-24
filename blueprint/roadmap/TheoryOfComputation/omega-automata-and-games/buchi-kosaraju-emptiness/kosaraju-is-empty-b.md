# Kosaraju-based Büchi emptiness scanner

Let a Büchi automaton have a finite alphabet, a state type with decidable equality and a Boolean
equality test `==` that agrees with equality and a hash function, and decidable transitions; let a
duplicate-free list enumerate all its states. Assume membership in the start and accepting sets is
decidable. The scanner computes the Kosaraju–Sharir blocks of the automaton's transition graph and
the set of states reachable from a start state by one depth-first search, and returns true exactly
when no block both passes the cyclicity test (length at least two, or a state with a self-loop) and
contains a state that is both accepting and reachable.
