# Razborov: monotone circuits for bipartite perfect matching need size n^{Ω(log n)}

Let $\mathrm{PM}_n$ be the Boolean function on the $n^2$ edge variables of subgraphs of $K_{n,n}$ that is $1$ iff the graph has a perfect matching. Every monotone circuit computing $\mathrm{PM}_n$ has size $n^{\Omega(\log n)}$; explicitly, more than $2^{\lfloor\lfloor\log_2 n\rfloor/16\rfloor\cdot c\log_2 n}$ gates for a fixed constant $c>0$ and all large $n$.

## Proof sketch

Method of approximations with approximators that are families of small matchings (at most $s=\Theta(\log n)$ edges), closed under a sunflower-type plucking (or closure) operation. Positive tests are the $n!$ perfect matchings, each missed by few approximator steps; negative tests are graphs induced by $2$-colourings of the vertices with an odd colour class, each wrongly accepted with small probability. Balancing the two error budgets gives the bound.

## Depends on

- [Monotone circuits](../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)
- [Perfect matching](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/perfect-matching.md)

## Proof depends on

- [Local approximation schemes (Razborov's method of approximations)](local-approximation-schemes.md)
- [Erdős–Rado sunflower lemma](../../../Combinatorics/extremal-set-theory/intersecting-families/sunflower-lemma/exists-is-delta-system.md)

## Sources

- Alexander A. Razborov, "Lower Bounds on Monotone Complexity of the Logical Permanent", Mathematical Notes of the Academy of Sciences of the USSR, 1985.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Noga Alon, Ravi B. Boppana, "The Monotone Circuit Complexity of Boolean Functions", Combinatorica, 1987.
