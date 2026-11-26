# Göös–Kamath–Robere–Sokolov: monotone complexity measures as TFNP subclasses

For a monotone function $f$ let $\mathrm{mKW}_f$ be its monotone Karchmer-Wigderson search problem. Then monotone circuit size, monotone formula size and monotone span program size over $\mathbb{F}_2$ of $f$ are each characterized, up to polynomial factors, by the least size of a reduction from $\mathrm{mKW}_f$ to a canonical search problem of a two-party TFNP subclass: respectively the communication analogue $\mathrm{PLS}^{\mathrm{cc}}$ of $\mathrm{PLS}$ (dag-like protocols; Razborov), the analogue $\mathrm{FP}^{\mathrm{cc}}$ of $\mathrm{FP}$ (protocols; Karchmer-Wigderson), and the analogue $\mathrm{PPA}^{\mathrm{cc}}$ of $\mathrm{PPA}$ (Göös-Kamath-Robere-Sokolov).

## Proof sketch

Each monotone model has a dual description as a cover of the $1$-inputs versus $0$-inputs structure with local consistency conditions. For span programs, the linear-algebraic dual is a parity argument over a graph with odd-degree sources, giving a $\mathrm{PPA}$-type reduction. Converses build the monotone object from the reduction by standard rectangle-to-gate translations.

## Depends on

- [Search problems: FNP, FP and TFNP](../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [Rectangle-DAGs (dag-like communication protocols)](../../communication-complexity/randomized-and-dag-like-lifting/rectangle-dag.md)
- [Deterministic communication complexity](../../communication-complexity/deterministic-communication-protocols/comm-complexity.md)

## Proof depends on

- [Monotone circuits are rectangle-DAGs for monotone Karchmer–Wigderson games](../../communication-complexity/randomized-and-dag-like-lifting/monotone-circuit-rectangle-dag.md)

## Sources

- M. Göös, P. Kamath, R. Robere, D. Sokolov, "Adventures in monotone complexity and TFNP", ITCS (2019).
- M. Karchmer, A. Wigderson, "Monotone circuits for connectivity require super-logarithmic depth", SIAM Journal on Discrete Mathematics 3 (1990) 255-265.
- A. A. Razborov, "Unprovability of lower bounds on circuit size in certain fragments of bounded arithmetic", Izvestiya: Mathematics 59 (1995) 205-227.
