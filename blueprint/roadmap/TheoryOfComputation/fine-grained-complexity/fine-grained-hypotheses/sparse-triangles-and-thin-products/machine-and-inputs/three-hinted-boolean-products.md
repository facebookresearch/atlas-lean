# Phased hinted Boolean matrix products

Take $n\ge1$. Width parameters are $t=\lfloor n^\tau\rfloor$ or $t_a=\lfloor n^{\tau_a}\rfloor$. Each phase has one fixed program and inherits memory from the last. Its input is supplied only at the start of the phase in the next unused cells following earlier inputs (overwriting whatever was there), and every phase must accept. Its time bound has form $C(n^a+1)$ with one common $C$; initialization time is uncharged and allowable width is every $W\ge b(\lfloor\log_2 n\rfloor+1)$. The first phase receives the dimensions and takes polynomial time.

- **Vector hint:** phase 1 also receives an $n\times t$ Boolean matrix $M$, phase 2 a $t\times n$ matrix $V$, phase 3 a column index $i$. Output the column $MV_{*,i}$ over the Boolean semiring.
- **Matrix-vector hint:** phase 1 also receives $N$ of shape $n\times n$ and $V$ of shape $t\times n$, phase 2 a list $I$ of $t$ column indices into $N$, phase 3 a column index $j$. Output $N_{*,I}V_{*,j}$.
- **Vector-matrix-vector hint:** phase 1 also receives $U,N,V$ of shapes $n\times t_1,n\times n,t_2\times n$, phase 2 a list $I$ of $t_1$ row indices into $N$, phase 3 a list $J$ of $t_2$ column indices, phase 4 indices $i,j$; output $(UN_{I,J}V)_{ij}$. Index lists may repeat entries. Matrices are row-major with Boolean entries encoded by 0 and 1. Output is immediately after the last input.

## Depends on

- [Restricted integer word RAM](restricted-integer-word-ram.md)

## Expansion

Implement fixed programs for each phase with the promise that later inputs are inaccessible until supplied. Isolate phase-wise time and prove output correctness for all valid hints, including repetitions.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [phase semantics](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3384-L3431) and [the three hint problems](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3621-L3694).
