# Feasible EUMORPHOUS TREE LAYOUT instances

An instance consists of a rooted binary tree on the vertices $0, \dots, n-1$, in which each child is marked as the left or the right child of its parent, and a positive integer $K$. The level of a vertex is its depth: the root has level $0$ and a child has its parent's level plus one. The instance is feasible when there is an injective assignment of a grid point $(x_v, y_v) \in \mathbb{Z} \times \mathbb{Z}$ to every vertex $v$ such that:

- (width) for some integer $a$, every vertex has $a \le x_v \le a + K$; the height is not bounded;
- (levels) the root has $y$-coordinate $0$ and every child lies one unit above its parent, $y_c = y_p + 1$, so $y_v$ is the level of $v$;
- (spacing) any two distinct vertices with the same $y$-coordinate satisfy $|x_u - x_v| \ge 2$;
- (sides) a right child $c$ of $p$ has $x_p < x_c$, a left child $c$ of $p$ has $x_c < x_p$, and a parent with a left child $\ell$ and a right child $r$ is centred between them, $x_p - x_\ell = x_r - x_p$;
- (no crossings) whenever $c_1$ is a child of $p_1$ and $c_2$ is a child of $p_2$, with $y_{p_1} = y_{p_2}$ and $x_{p_1} < x_{p_2}$, then $x_{c_1} < x_{c_2}$: children of parents on one level appear in the same left-to-right order as their parents, which for straight-line edges says that no two edges cross;
- (isomorphic subtrees) whenever a map $\varphi$ sends the subtree rooted at $u$ onto the subtree rooted at $v$ as a binary tree, preserving left and right children (it sends $u$ to $v$, the child on each side of a descendant $w$ to the child on the same side of $\varphi(w)$, and $\varphi(w)$ has a child on a side only if $w$ does), there is a vector $d \in \mathbb{Z} \times \mathbb{Z}$ with $(x_{\varphi(w)}, y_{\varphi(w)}) = (x_w, y_w) + d$ for every descendant $w$ of $u$, including $u$ itself.
