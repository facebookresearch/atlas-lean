# Thin products, lopsided triangles, and persistent queries

A thin matrix input is a pair of integer matrices $X$ of shape $N\times D$ and $Y$ of shape $D\times N$, with every entry of absolute value at most an auxiliary $U$. An offline list $W$ of pairs of indices in $[N]^2$ has no duplicates. The input is $N,D,|W|$, any specified auxiliary parameters, then the two row-major matrices, then all row indices followed by all column indices of $W$. Accept and output the entries of $XY$ in the order of $W$. For the lopsided triangle versions the two matrices have entries 0 or 1 and $U=1$: a pair $(i,j)$ is queried for common middle vertices $h$ such that $X_{ih}=Y_{hj}=1$. Counting outputs the number of such vertices and detection outputs 1 iff there is one. A smaller middle part may be padded with isolated vertices.

The data-structure version preprocesses $N,D$, any auxiliary parameters, and the matrix pair; the query indices are not known at this stage. Its time bound $T_p$ is a bound on the halting time of accepting preprocessing. If its input takes cells $0$ through $\ell-1$, the preprocessing must leave every cell $a<-S_p$ or $a>\ell+S_p$ unchanged. At each query, the two indices are placed in fixed cells; the query program restarts on the resulting memory and must accept within its bound $T_q$ and write the exact answer to a fixed output cell. All finite sequences of valid queries work, retaining the memory left by the preceding query. The space condition applies to preprocessing's final memory, not all intermediate or query writes.

## Depends on

- [Restricted integer word RAM](restricted-integer-word-ram.md)

## Expansion

Formalize the matrix layouts and bounds together with persistent query memory, and prove the single-query correctness invariant stable under every finite sequence.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [thin input, answer and query semantics](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3366-L3558).
