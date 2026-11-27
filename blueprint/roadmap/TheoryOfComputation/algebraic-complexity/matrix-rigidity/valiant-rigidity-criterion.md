# Valiant's rigidity criterion for linear circuits

Let $A$ be an $n\times n$ matrix over a field, and suppose the linear map $x\mapsto Ax$ is computed by a linear circuit (gates computing linear combinations of their arguments) of fan-in two with $s$ edges and depth $d$. Then for every $t\ge1$,

$$
R_A\Bigl(\frac{s\log_2 t}{\log_2 d}\Bigr)\le n\cdot 2^{O(d/t)} .
$$

In particular, if $A$ has linear circuits of size $O(n)$ and depth $O(\log n)$, then $R_A(\varepsilon n)\le n^{1+o(1)}$ for every fixed $\varepsilon>0$; contrapositively, a matrix with $R_A(\varepsilon n)\ge n^{1+\delta}$ for some $\varepsilon,\delta>0$ has no linear circuits of linear size and logarithmic depth.

## Proof sketch

By the Erdős–Graham–Szemerédi lemma, removing $s\log_2t/\log_2d$ edges from a DAG with $s$ edges and depth $d$ leaves a DAG of depth at most $d/t$. The values carried by the removed edges are linear forms spanning a space of dimension at most their number, giving a low-rank part; in the remaining DAG every output depends on at most $2^{d/t}$ inputs, giving a matrix with at most $n2^{d/t}$ nonzero entries.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)
- [Affine circuits compute affine maps](../../circuit-complexity/circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/simulations-between-circuit-bases/affine-circuits-compute-affine-maps.md)

## Sources

- Leslie G. Valiant, "Graph-Theoretic Arguments in Low-Level Complexity", Mathematical Foundations of Computer Science 1977, 1977.
- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
