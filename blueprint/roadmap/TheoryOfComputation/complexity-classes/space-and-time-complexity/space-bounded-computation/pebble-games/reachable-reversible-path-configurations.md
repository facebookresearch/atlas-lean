# Characterization of reachable reversible pebblings of the path

In the reversible pebble game on the directed path with $n$ pebbles, a configuration $C$ with $f=n-|C|$ free pebbles is reachable from $\emptyset$ iff it has a **removal numbering**: a bijection numbering the pebbles of $C$ by $f,\dots,n-1$ such that each pebble numbered $i$ has a higher-numbered pebble, or the path start, at most $2^{i}$ positions to its left. Equivalently, $C$ is weakly solvable (some sequence of 'big steps', each removing an available pebble with the free pebbles, frees every pebble) iff it is strongly solvable (no such sequence gets stuck); in particular greedy removal of the leftmost available pebble decides reachability.

## Proof sketch

Big steps played backwards are runs, so solvable configurations are reachable. Conversely each move places or removes an available pebble; placing preserves solvability, and removing preserves it by shifting the numbers of lower-numbered pebbles up by one and following the chain of witnesses to the left, whose total length is at most $2^{i+1}$.

## Depends on

- [Bennett's reversible pebble game](reversible-pebble-game.md)

## Proof depends on

- [Li–Tromp–Vitányi: reversible pebbling of the path needs logarithmically many pebbles](reversible-pebbling-of-the-path.md)

## Sources

- Ming Li, John Tromp and Paul Vitányi, "Reversible Simulation of Irreversible Computation by Pebble Games", Physica D: Nonlinear Phenomena 120, arXiv:quant-ph/9703009, 1998.
