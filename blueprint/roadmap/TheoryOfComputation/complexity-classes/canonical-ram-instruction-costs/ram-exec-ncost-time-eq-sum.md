# The time charged by a bounded RAM run

For a program of length $\ell$, a budget $b$ and an initial state $s$ of the canonical random-access machine, the time annotation of the cost-annotated run of $b$ steps has first component equal to the number of $k < b$ for which the program counter after $k$ plain steps from $s$ is below $\ell$, and its other two components equal to $0$. These other components are bookkeeping fields with no modelled meaning, not measurements of physical resources.
