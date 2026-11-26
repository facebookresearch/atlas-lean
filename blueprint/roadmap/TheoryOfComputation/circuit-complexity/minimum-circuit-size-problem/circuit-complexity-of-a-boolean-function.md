# Circuit complexity of a Boolean function and truth tables

A *De Morgan circuit* on $n$ inputs is a straight-line program whose gates are binary AND, binary OR, NOT and the constants, over the input variables. Its *size* counts all gates. The *circuit complexity* $\mathrm{CC}(f)$ of $f : \{0,1\}^n \to \{0,1\}$ is the least size of a circuit computing $f$; for a set $S \subseteq \{0,1\}^n$, $\mathrm{CC}_S(f)$ is the least size of a circuit agreeing with $f$ on $S$. The *truth table* of $f$ is the string $\mathrm{tt}(f) \in \{0,1\}^{2^n}$ listing $f(x)$ for $x$ in lexicographic order; strings of length $N = 2^n$ are identified with truth tables. A *De Morgan formula* is a circuit whose gates have fan-out one; its *leaf size* is its number of input leaves.

## Depends on

- [Boolean gates](../boolean-circuits/boolean-gate.md)
- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- V. Kabanets and J.-Y. Cai, "Circuit Minimization Problem", STOC 2000.
