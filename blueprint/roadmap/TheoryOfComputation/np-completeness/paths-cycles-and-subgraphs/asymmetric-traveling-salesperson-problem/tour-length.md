# Length of a tour in the asymmetric TSP

Let $w$ be a weight matrix, given as a list of rows
of natural numbers, and let $t = (t_0, \dots, t_{L-1})$ be a list of natural numbers. The length
of the tour $t$ under $w$ is $\sum_{j=0}^{L-1} w_{t_j, t_{(j+1) \bmod L}}$, the sum of the weights
along the closed walk including the return edge from $t_{L-1}$ to $t_0$, where $w_{a,b}$ denotes
the entry in row $a$ and column $b$ of $w$, taken to be $0$ when that entry does not exist. In
particular the empty tour has length $0$.
