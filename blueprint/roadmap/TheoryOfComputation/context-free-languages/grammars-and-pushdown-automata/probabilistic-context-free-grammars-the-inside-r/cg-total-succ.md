# Recurrence for the total weight of bounded-depth binary trees

A one-nonterminal tree is a finite binary tree: either a leaf or a node with a left and a right subtree. Its depth is $1$ for a leaf and one more than the larger depth of the subtrees for a node. For reals $p$ and $q$, its weight is $q$ for a leaf and $p$ times the weights of the two subtrees for a node. Let $T_h$ be the total weight of the one-nonterminal trees of depth at most $h$. For all reals $p, q$ and every $h$, $T_{h+1} = q + p\,T_h^2$.
