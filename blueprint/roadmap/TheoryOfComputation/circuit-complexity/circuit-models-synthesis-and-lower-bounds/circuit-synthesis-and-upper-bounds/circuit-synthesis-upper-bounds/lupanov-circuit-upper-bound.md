# Lupanov's asymptotic circuit upper bound

For every $\varepsilon>0$ there is $n_0$ such that for all $n\ge n_0$ every Boolean function $f:\{0,1\}^n\to\{0,1\}$ has a circuit over the De Morgan basis of size at most $(1+\varepsilon)\,2^n/n$, where every gate counts, negations and constants included; a fortiori the same bound holds when negations and constants are free. Together with Shannon's counting bound (whose counting argument also applies when negations are free) this shows that the maximal circuit complexity of $n$-variable functions is $(1+o(1))2^n/n$.

## Proof sketch

Lupanov's local coding, as presented by Jukna: write $f=\bigvee_a K_a(x_1,\dots,x_k)\wedge f_a(x_{k+1},\dots,x_n)$ over the minterms $K_a$ of the first $k$ variables. Cut the $2^{n-k}$ values of each $f_a$ into consecutive intervals of length $m$ and write $f_a$ as the disjunction of its pieces $f_{a,i}$, each vanishing outside the $i$-th interval; for each $i$ there are at most $2^{m+1}$ such pieces, and all of them are computed once from the minterms of the last $n-k$ variables. Each $f_a$ is then an OR of $2^{n-k}/m$ shared pieces, and the total is $2^n/m+O(2^n/n^2)$ gates; $k=n-2\log_2 n$ and $m=n-4\log_2 n$ give $(1+O(\log n/n))\,2^n/n$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [All minterms in linear size](all-minterms-in-linear-size.md)
- [Shannon's sharp counting bound: almost all functions need more than 2^n/n gates](../../circuit-models-and-classes/circuit-models-and-complexity-measures/shannon-sharp-circuit-size-lower-bound.md)

## Sources

- CSLib, `Cslib.Circuits.Boolean.Lupanov.exists_circuit` (module `Cslib.Computability.Circuit.Boolean.Lupanov`): the upper bound with every gate counted.
- Oleg B. Lupanov, "On a Method of Circuit Synthesis", Izvestiya Vysshikh Uchebnykh Zavedenii. Radiofizika 1(1), 120–140, 1958.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987.
