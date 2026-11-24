# The Kosaraju scanner detects reachable accepting cyclic blocks

Let a Büchi automaton have a finite alphabet, a state type with decidable equality and a Boolean
equality test `==` that agrees with equality and a hash function, and decidable transitions; let a
duplicate-free list enumerate all its states. Call a list of vertices of a directed graph cyclic
when it contains two distinct vertices or a vertex with a self-loop. Assume membership in the start
and accepting sets is decidable, and that every block of the Kosaraju–Sharir decomposition of the
transition graph is duplicate-free. Then the Kosaraju emptiness scanner returns true if and only if
there is no block that is cyclic and contains a state that is accepting and reachable from a start
state.
