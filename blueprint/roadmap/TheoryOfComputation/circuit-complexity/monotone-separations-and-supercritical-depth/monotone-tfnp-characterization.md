# Göös–Kamath–Robere–Sokolov: monotone complexity measures as TFNP subclasses

For a monotone function $f$ let $\mathrm{mKW}_f$ be its monotone Karchmer-Wigderson search problem. Then monotone circuit size, monotone formula size, monotone span program size over $\mathbb{F}_2$ and monotone switching network size of $f$ are each characterized, up to polynomial factors, by the least size of a reduction from $\mathrm{mKW}_f$ to a canonical search problem of a two-party TFNP subclass: respectively to dag-like protocols (a communication analogue of $\mathrm{PLS}$), protocols (the analogue of $\mathrm{FP}$), $\mathrm{PPA}$-type parity problems, and $\mathrm{PPAD}$-type end-of-line problems ($\mathrm{EoML}$).

## Proof sketch

Each monotone model has a dual description as a cover of the $1$-inputs versus $0$-inputs structure with local consistency conditions. For span programs, the linear-algebraic dual is a parity argument over a graph with odd-degree sources, giving a $\mathrm{PPA}$-type reduction; for switching networks, the reachability structure yields an end-of-line instance. Converses build the monotone object from the reduction by standard rectangle-to-gate translations.

## Depends on

- [Monotone circuits are rectangle-DAGs for monotone Karchmer–Wigderson games](../../communication-complexity/randomized-and-dag-like-lifting/monotone-circuit-rectangle-dag.md)
- [Search problems: FNP, FP and TFNP](../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Proof depends on

- [Monotone circuits are rectangle-DAGs for monotone Karchmer–Wigderson games](../../communication-complexity/randomized-and-dag-like-lifting/monotone-circuit-rectangle-dag.md)
- [Search problems: FNP, FP and TFNP](../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- M. Göös, P. Kamath, R. Robere, D. Sokolov, "Adventures in monotone complexity and TFNP", ITCS (2019).
