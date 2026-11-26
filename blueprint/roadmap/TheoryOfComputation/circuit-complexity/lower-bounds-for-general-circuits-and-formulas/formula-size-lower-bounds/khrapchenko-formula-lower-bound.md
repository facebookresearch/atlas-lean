# Khrapchenko's formula lower bound

Let $A\subseteq f^{-1}(1)$ and $B\subseteq f^{-1}(0)$ be nonempty sets of inputs of a Boolean function $f$ on $n$ bits, and let $E(A,B)$ be the set of pairs $(a,b)\in A\times B$ at Hamming distance one. Then every De Morgan formula computing $f$ has at least

$$
\frac{|E(A,B)|^2}{|A|\,|B|}
$$

leaves.

## Proof sketch

The measure $\mu(A,B)=|E(A,B)|^2/(|A||B|)$ is at most one on every rectangle separated by a literal and is subadditive under the splitting of $(A,B)$ induced by an AND or OR gate (by the Cauchy–Schwarz inequality), so induction on the formula gives the bound. Equivalently, it is a formal complexity measure bound.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- V. M. Khrapchenko, "Complexity of the realization of a linear function in the class of Π-circuits", Mathematical Notes of the Academy of Sciences of the USSR, 1971.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
