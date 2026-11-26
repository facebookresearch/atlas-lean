# The smaller-half counting lemma

Let $Q$ be a finite set, $q \in Q$, $k \in \mathbb{N}$, and $f_0, f_1, \dots$ subsets of $Q$ such that $q \in f_i$ for
all $i \le k$ and $2|f_{i+1}| \le |f_i|$ for all $i < k$. Then $k \le \lfloor \log_2 |Q| \rfloor$.

In Hopcroft's algorithm the successive smaller halves containing a fixed state form such a chain.

## Sources

- J. E. Hopcroft, "An `n log n` algorithm for minimizing states in a finite automaton", Theory of Machines and Computations, 1971; the counting argument is presented in J. Berstel, L. Boasson, O. Carton and I. Fagnot, "Minimization of automata", 2010.
