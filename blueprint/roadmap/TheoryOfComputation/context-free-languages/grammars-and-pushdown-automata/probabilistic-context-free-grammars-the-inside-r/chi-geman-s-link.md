# Cutoff sums are total weights of bounded-depth trees

A one-nonterminal tree is a finite binary tree: either a leaf or a node with a left and a right subtree. Its depth is $1$ for a leaf and one more than the larger depth of the subtrees for a node. For reals $p$ and $q$, its weight is $q$ for a leaf and $p$ times the weights of the two subtrees for a node. Define $S_0 = S_1 = 0$ and $S_{h+1} = q + p\,S_h^2$ for $h \ge 1$. For all reals $p, q$ and every $h$, $S_{h+1}$ equals the total weight of the trees of depth at most $h$.
