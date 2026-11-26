# Integer problems on the restricted word RAM

For Exact Triangle the input after $n$ is three $n\times n$ matrices in row order. Accept if some $i,j,k$ have $A_{ij}+B_{jk}+C_{ik}=0$. The separate graph version uses a simple undirected graph, a symmetric integer weight matrix, and asks for three pairwise adjacent vertices with total weight zero; input is the adjacency matrix then weights (zero for nonedges). For 3SUM the input is a list of $n$ integers; seek three **distinct positions**, not necessarily distinct values, that sum to zero.

For the min-plus product input two $n\times n$ integer matrices in row order; output in that order $\min_k (A_{ik}+B_{kj})$. For APSP input the directed adjacency matrix and then integer weights (zero for absent edges). Walks may repeat vertices and the empty walk has weight zero. Every closed walk is assumed nonnegative. For each ordered pair in row order output a reachability flag and, if reachable, the minimum attainable walk weight; the distance cell is unconstrained if unreachable.

For $k$-partite clique the parts are all labeled and each has $n$ vertices. Supply the $k^2$ ordered blocks of edge weights, in block and row order (even unused blocks are subject to the weight bound). For a selection $(v_1,\ldots,v_k)$ sum precisely the weights between parts $i<j$ at $(v_i,v_j)$. Zero-weight detection accepts iff some selection has weight zero; minimum/maximum outputs the $k$ selected indices and requires $n\ge1$.

## Depends on

- [Restricted integer word RAM](restricted-integer-word-ram.md)

## Expansion

Represent the instance encodings and compare them to existing graph and matrix interfaces; verify the promised distinction between an absent edge and weight zero. For APSP prove that minima are attained under the nonnegative closed-walk promise.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [fixed layouts and decision/optimization semantics](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/EndStatement.lean#L69-L137) and [graph and extremal versions](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3561-L3617).
