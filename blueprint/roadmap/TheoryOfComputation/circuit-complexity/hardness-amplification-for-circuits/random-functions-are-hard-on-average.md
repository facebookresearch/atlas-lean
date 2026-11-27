# Random functions are hard on average

For every $n\ge 400$ there is a Boolean function $f$ on $n$ bits with $H_{\mathrm{avg}}(f)\ge 2^{n/10}$: for $S=\lceil 2^{n/10}\rceil$, every De Morgan circuit with at most $S$ gates agrees with $f$ on fewer than a $\tfrac12+\tfrac1S$ fraction of the inputs.

## Proof sketch

For a fixed circuit, a uniformly random $f$ agrees with it on at least $\tfrac12+\tfrac1S$ of the inputs with probability at most $e^{-2^{n+1}/S^2}$ by Hoeffding's inequality. There are at most $2^{O(S\log S)}$ circuits of size $S$, so a union bound leaves positive probability for $S=2^{n/10}$.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)

## Proof depends on

- [Counting functions with small De Morgan circuits](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/counting-functions-with-small-circuits.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009 (exercise on random functions with $H_{\mathrm{avg}}\ge 2^{n/10}$; Chapter 16, Exercise 3 in the 2007 web draft).
