# The binary trees of depth at most h

A one-nonterminal tree is a finite binary tree: either a leaf or a node with a left and a right subtree. Its depth is $1$ for a leaf and one more than the larger depth of the subtrees for a node. For reals $p$ and $q$, its weight is $q$ for a leaf and $p$ times the weights of the two subtrees for a node. The finite set of trees of depth at most $h$ is defined by recursion: it is empty for $h = 0$, and for $h + 1$ it consists of the leaf and all nodes whose two subtrees lie in the set for $h$.
