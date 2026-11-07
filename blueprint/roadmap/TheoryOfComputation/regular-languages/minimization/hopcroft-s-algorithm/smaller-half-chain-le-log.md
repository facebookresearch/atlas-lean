# The smaller-half counting lemma

In a chain of blocks where each step at least
halves the size, a block containing a given state can occur at most `Nat.log 2 n` times
past the start, where `n` is the number of states. In Hopcroft's algorithm, the successive
smaller halves containing one fixed state form such a chain: each of them is the smaller
half of a split of the previous block containing that state.

## Sources

- J. E. Hopcroft, "An `n log n` algorithm for minimizing states in a finite automaton", Theory of Machines and Computations, 1971; the counting argument is presented in J. Berstel, L. Boasson, O. Carton and I. Fagnot, "Minimization of automata", 2010.
