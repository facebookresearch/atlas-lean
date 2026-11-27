# The emptiness test decides emptiness of DFAs

Let $M$ be a DFA over a finite alphabet
with finitely many states. The emptiness test applied to $M$ returns true if and only if the
language accepted by $M$ is empty.

## Sources

- M. O. Rabin and D. Scott, *Finite automata and their decision problems*, IBM Journal of Research and Development 3(2) (April 1959), 114–125, Corollary 7.1 (p. 119): emptiness of $T(\mathfrak{A})$ is decidable. Rabin and Scott
  decide it by trying the tapes shorter than the number of states (Theorem 7); the test here
  searches the reachable states instead.
