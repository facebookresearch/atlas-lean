# Li–Tromp–Vitányi: reversible pebbling of the path needs logarithmically many pebbles

On the directed path $0\to1\to2\to\cdots$, with $k$ pebbles: a configuration containing $v$ is reachable iff $v+2\le 2^{k}$, and the configuration $\{v\}$ is reachable iff $2(v+1)\le 2^{k}$. Hence the reversible pebbling price of $v$ is $\lceil\log_2(v+2)\rceil$ and its persistent price is $\lceil\log_2(v+1)\rceil+1$, whereas every non-source vertex has black pebbling price $2$. Bennett's recursive strategy pebbles a block of $2^{k}$ consecutive vertices with $k+1$ extra pebbles in $3^{k}$ moves, ending with only its last vertex pebbled.

## Proof sketch

Bennett: pebble the midpoint recursively, pebble the end from the midpoint recursively, then run the first stage backwards; the move count satisfies $T(k)=3T(k-1)$, $T(0)=1$. Both thresholds follow from the characterization of reachable configurations, with the start of the path counted as a permanent pebble at position $-1$: a configuration containing $v$ needs pebbles numbered so that the chain of gaps from $v$ back to $-1$ is at most $2^{0}+2^{1}+\dots+2^{k-1}=2^{k}-1$, i.e. $v+1\le 2^{k}-1$; the single pebble of $\{v\}$ carries the number $k-1$, so it is reachable iff $v+1\le 2^{k-1}$.

## Depends on

- [Bennett's reversible pebble game](reversible-pebble-game.md)

## Proof depends on

- [Characterization of reachable reversible pebblings of the path](reachable-reversible-path-configurations.md)

## Sources

- Ming Li, John Tromp and Paul Vitányi, "Reversible Simulation of Irreversible Computation", Physica D: Nonlinear Phenomena 120(1–2), arXiv:quant-ph/9703009, 1998, Section 7, Corollaries 1 and 2.
- Charles H. Bennett, "Time/Space Trade-Offs for Reversible Computation", SIAM Journal on Computing 18(4), 1989.
