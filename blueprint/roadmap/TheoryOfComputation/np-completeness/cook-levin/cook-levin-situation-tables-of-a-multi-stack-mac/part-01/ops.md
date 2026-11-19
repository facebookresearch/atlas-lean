# Stack operations on a path of a statement tree

For a statement tree $q$ of a multi-stack
Turing machine, $\operatorname{ops}(q)$ is the largest number of push, peek and pop nodes on a path
from the root of $q$ to a leaf. Load and branch nodes do not count, and goto and halt leaves
contribute $0$.
