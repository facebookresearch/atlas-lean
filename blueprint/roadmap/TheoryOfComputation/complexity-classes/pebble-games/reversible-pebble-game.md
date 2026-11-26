# Bennett's reversible pebble game

The **reversible pebble game** on a DAG $G$ has the same configurations as the black pebble game, but both placing a pebble on $v$ and removing the pebble from $v$ require all predecessors of $v$ to be pebbled. Hence every move is undone by the opposite move and, on loopless graphs, every run can be reversed with the same budget. A vertex $v$ is reversibly pebblable with $s$ pebbles if some run from $\emptyset$ with at most $s$ pebbles reaches a configuration containing $v$, and **persistently** pebblable if the run ends in the configuration $\{v\}$. The reversible and persistent prices are the least such $s$. Every reversible run is a black run, so the reversible price is at least the black price.

## Depends on

- [Black pebble game and black pebbling price](black-pebble-game.md)

## Sources

- Charles H. Bennett, "Time/Space Trade-Offs for Reversible Computation", SIAM Journal on Computing 18(4), 1989.
- Ming Li, John Tromp and Paul Vitányi, "Reversible Simulation of Irreversible Computation by Pebble Games", Physica D: Nonlinear Phenomena 120, arXiv:quant-ph/9703009, 1998.
