# Time-block computations are implicit Tree Evaluation instances

Let $M$ be a deterministic multi-tape Turing machine running for $t$ steps, and split the run into $T=\lceil t/b\rceil$ time blocks of $b$ steps. For each block $i$ let $\beta_i$ be the content of the $O(b)$-cell work-tape window visited during block $i$ together with head positions and state at its end. Then each $\beta_i$ is a fixed function, computable in space $O(b)$ from the input, of the $O(1)$ earlier block summaries $\beta_j$ that last wrote to the cells touched in block $i$ (Hopcroft–Paul–Valiant). Unrolling these dependencies gives a Tree Evaluation instance of height $O(T)$, fan-in $O(1)$ and value length $O(b)$ whose root value determines the output of $M$, and each gate entry is computable from the input in small space.

## Proof sketch

In a time block the heads move at most $b$ cells, so the window is determined by the previous window of each tape and by which earlier blocks last visited the relevant cells; this dependency graph is a DAG of in-degree $O(1)$, which is unfolded into a tree.

## Depends on

- [The Tree Evaluation problem](tree-evaluation-problem.md)
- [Deterministic time classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- John Hopcroft, Wolfgang Paul and Leslie Valiant, "On Time Versus Space", Journal of the ACM 24(2), 1977.
- Ryan Williams, "Simulating Time With Square-Root Space", Proceedings of the 57th Annual ACM Symposium on Theory of Computing (STOC 2025), 2025.
