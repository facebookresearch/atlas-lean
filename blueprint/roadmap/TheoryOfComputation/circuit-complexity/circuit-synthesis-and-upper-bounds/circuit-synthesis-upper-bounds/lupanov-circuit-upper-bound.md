# Lupanov's asymptotic circuit upper bound

For every $\varepsilon>0$ there is $n_0$ such that for all $n\ge n_0$ every Boolean function $f:\{0,1\}^n\to\{0,1\}$ has a circuit over the De Morgan basis (with negations and constants free) of size at most $(1+\varepsilon)\,2^n/n$. Together with Shannon's counting bound this shows that the maximal circuit complexity of $n$-variable functions is $(1+o(1))2^n/n$.

## Proof sketch

Lupanov's local coding: split the truth table into strips of $s\approx n-3\log n$ rows, compute all minterms of the row variables, and for each strip encode its columns by $O(2^s/s)$ distinct patterns, each realized once as a disjunction of minterms and then selected by the column variables.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Shannon's sharp counting bound: almost all functions need more than 2^n/n gates](../../circuit-models-and-classes/circuit-models-and-complexity-measures/shannon-sharp-circuit-size-lower-bound.md)

## Sources

- Oleg B. Lupanov, "On a Method of Circuit Synthesis", Izvestiya Vysshikh Uchebnykh Zavedenii. Radiofizika, 1958.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987.
