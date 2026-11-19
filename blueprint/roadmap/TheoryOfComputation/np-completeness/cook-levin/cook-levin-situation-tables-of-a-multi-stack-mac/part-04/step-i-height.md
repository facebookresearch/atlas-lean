# Stack heights grow by at most the window depth per step

Let $M$ be a finite multi-stack
Turing machine (finitely many stacks, labels and states, and a finite input alphabet), and let $d$
be its window depth, the largest number of push, peek and pop nodes on a root-to-leaf path of any
of its statement trees. For every configuration $c$ of $M$ and every stack $k$, the length of
stack $k$ after one idle-extended step of $M$ from $c$ is at most the length of stack $k$ of $c$
plus $d$.
