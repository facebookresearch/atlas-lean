# Characterization of reachable reversible pebblings of the path

Consider the reversible pebble game on the directed path $0\to1\to2\to\cdots$ with $n$ pebbles, and treat the start of the path as a permanently pebbled position $-1$ (so vertex $0$ may be pebbled or unpebbled at any time). A configuration $C$ with $f=n-|C|$ free pebbles is reachable from $\emptyset$ iff its pebbles can be numbered $f,f+1,\dots,n-1$ so that each pebble numbered $i$ has a higher-numbered pebble, or the permanent pebble at $-1$, at most $2^{i}$ positions to its left. Call a pebble **available** when, with $f$ free pebbles, some pebble lies at most $2^{f}$ positions to its left, and a configuration **weakly** (resp. **strongly**) **solvable** if some (resp. every) sequence of removals of available pebbles frees all pebbles. Every weakly solvable configuration is strongly solvable, so greedy removal of any available pebble decides reachability.

## Proof sketch

With $f$ free pebbles, Bennett's recursive procedure removes an available pebble, and running it backwards places one, so weakly solvable configurations are reachable. For the converse it suffices that weak solvability is preserved by every move; adding a pebble clearly preserves it, and removing one is handled by showing weak implies strong solvability: if an available pebble $g$ is removed out of order, a pebble $j<g$ that relied on $g$ later finds a higher-numbered pebble at distance at most $2^{j}+2^{f}+\dots+2^{j-1}\le 2^{j+1}$, which is within range once $g$ is free.

## Depends on

- [Bennett's reversible pebble game](reversible-pebble-game.md)

## Sources

- Ming Li, John Tromp and Paul Vitányi, "Reversible Simulation of Irreversible Computation", Physica D: Nonlinear Phenomena 120(1–2), arXiv:quant-ph/9703009, 1998, Section 7, Theorem 1 and Corollary 1.
