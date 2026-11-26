# Nearest-neighbor interchange on a graph

For a graph $G$ and vertices $u, v, b, c$, the swapped graph deletes the edges $ub$ and $vc$ from $G$ and adds the edges $uc$ and $vb$ (an edge between equal vertices is not added). The operation applies to any graph, even one without these edges. When $uv$ is an internal edge of an unrooted binary tree, $b \ne v$ is a neighbour of $u$ and $c \ne u$ a neighbour of $v$, it is the nearest-neighbour interchange that exchanges the subtree at $b$ with the subtree at $c$; that is how a [single nni step](is-nnistep.md) uses it.
