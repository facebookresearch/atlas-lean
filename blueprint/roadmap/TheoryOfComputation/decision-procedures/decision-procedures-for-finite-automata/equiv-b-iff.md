# Correctness of the equivalence test for DFAs

Let $M$ and $N$ be DFAs over the same finite
alphabet, with finite state sets with decidable equality and decidable sets of accepting states.
The equivalence test of $M$ and $N$ returns true if and only if $M$ and $N$ accept the same
language.

## Sources

- M. O. Rabin and D. Scott, *Finite automata and their decision problems*, IBM Journal of Research and Development 3(2) (April 1959), 114–125, Theorem 10 and Corollary 10.1 (p. 120): equivalence is decidable, through the direct
  product of one automaton with the complement of the other (Definition 7, Theorem 6). The test
  here uses the product automaton of the symmetric difference in the same way.
