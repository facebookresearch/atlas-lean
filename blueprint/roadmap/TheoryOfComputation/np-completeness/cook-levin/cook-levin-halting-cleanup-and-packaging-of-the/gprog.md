# The composed program

Let $g, r \in \mathbb{N}$, let $P$ be a program with labels
$\Lambda$ and Boolean state over the stacks of the full machine with alphabets $F\Gamma_{g,r}$,
and let $\mathit{fin} \in \Lambda$. The composed program has as labels the labels of $P$ and the
drain stages $0, \dots, n$, where $n$ is the number of stacks other than the output stack. At a
label $\ell \ne \mathit{fin}$ it runs $P(\ell)$ with every jump target relabelled; at
$\mathit{fin}$ it jumps to drain stage $0$; at drain stage $i < n$ it empties the $i$-th stack
other than the output stack (in a fixed order) and moves to stage $i + 1$, and at stage $n$ it
sets the state to false and halts.
