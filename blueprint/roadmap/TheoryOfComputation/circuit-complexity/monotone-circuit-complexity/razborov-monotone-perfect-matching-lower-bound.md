# Razborov: monotone circuits for bipartite perfect matching need size n^{Ω(log n)}

Let $\mathrm{PM}_n$ be the Boolean function on the $n^2$ edge variables of subgraphs of $K_{n,n}$ that is $1$ iff the graph has a perfect matching. Every monotone circuit computing $\mathrm{PM}_n$ has size $n^{\Omega(\log n)}$.

## Proof sketch

Razborov's method of approximations: every gate is replaced by an approximator, a monotone function spanned by families of small partial matchings (of size $\Theta(\log n)$), kept small by a sunflower-type closure operation. Positive test inputs are the perfect matchings and negative test inputs are suitably distributed graphs without a perfect matching. Each approximation step errs on few positive tests and on a small fraction of negative tests, while the final approximator is wrong on many tests of one kind; balancing the two error budgets forces $n^{\Omega(\log n)}$ gates.

## Depends on

- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)
- [Perfect matching](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/perfect-matching.md)

## Proof depends on

- [Local approximation schemes (Razborov's method of approximations)](local-approximation-schemes.md)
- [Erdős–Rado sunflower lemma](../../../Combinatorics/extremal-set-theory/intersecting-families/sunflower-lemma/exists-is-delta-system.md)

## Sources

- Alexander A. Razborov, "Lower Bounds on Monotone Complexity of the Logical Permanent", Mathematical Notes of the Academy of Sciences of the USSR 37(6), 1985.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012 (Section 9.10, Razborov's proof for perfect matching).
- Noga Alon, Ravi B. Boppana, "The Monotone Circuit Complexity of Boolean Functions", Combinatorica 7(1), 1987.
