# Li–Tromp–Vitányi: reversible pebbling of the path needs logarithmically many pebbles

On the directed path $0\to1\to2\to\cdots$, with $k$ pebbles: a configuration containing $v$ is reachable iff $v+2\le 2^{k}$, and the configuration $\{v\}$ is reachable iff $2(v+1)\le 2^{k}$. Hence the reversible pebbling price of $v$ is $\lceil\log_2(v+2)\rceil$ and its persistent price is $\lceil\log_2(v+1)\rceil+1$, whereas every non-source vertex has black pebbling price $2$. Bennett's recursive strategy pebbles a block of $2^{k}$ consecutive vertices with $k+1$ extra pebbles in $3^{k}$ moves, ending with only its last vertex pebbled.

## Proof sketch

Bennett: pebble the midpoint recursively, pebble the end from the midpoint recursively, then run the first stage backwards. Lower bound by induction on $k$: restrict a reversed run to the vertices below the least pebbled vertex, and a forward run to the vertices above $2^{k-1}$, each restriction using at most $k-1$ pebbles.

## Depends on

- [Bennett's reversible pebble game](reversible-pebble-game.md)

## Sources

- Ming Li, John Tromp and Paul Vitányi, "Reversible Simulation of Irreversible Computation by Pebble Games", Physica D: Nonlinear Phenomena 120, arXiv:quant-ph/9703009, 1998.
- Charles H. Bennett, "Time/Space Trade-Offs for Reversible Computation", SIAM Journal on Computing 18(4), 1989.
