# Korten's top-down lower bounds for constant depth

A circuit over the unbounded fan-in basis with $g$ gates, $n$ inputs and AND/OR depth $d$ (negations free) yields a Karchmer–Wigderson protocol with $d$ messages over an alphabet of size $n+g$: the players walk down from the output, at an AND gate the player whose input falsifies it naming a false argument, at an OR gate the player whose input satisfies it naming a true argument. Korten's theorem bounds such protocols for parity: for every $d\ge2$ there is $\varepsilon>0$ such that, for large $n$, every circuit of AND/OR depth $d$ computing parity (or majority) of $n$ bits has $n+g>2^{\varepsilon n^{1/(d-1)}}$. The same bound holds for alternating formulas of depth $d$ with $S$ gates: $S+2n+1>2^{\varepsilon n^{1/(d-1)}}$.

## Proof sketch

A protocol with few rounds over a small alphabet induces, round by round, a large rectangle of parity inputs on which the transcript is fixed; a combinatorial argument on the remaining free coordinates (in the spirit of a top-down switching argument) shows the final round cannot always name a differing coordinate unless the alphabet is exponentially large in $n^{1/(d-1)}$.

## Depends on

- [The Karchmer–Wigderson game of a Boolean function](karchmer-wigderson-game.md)
- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)

## Proof depends on

- [Karchmer–Wigderson: formula depth equals communication complexity](karchmer-wigderson-theorem.md)

## Sources

- Oliver Korten, "Top-Down Lower Bounds for All Depths", Electronic Colloquium on Computational Complexity, 2026.
