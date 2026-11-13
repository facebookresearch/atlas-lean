# The drain

Let $M$ be a multi-stack machine program with labels in a type $\Lambda$, let
$k_0, \dots, k_{m-1}$ be a list of distinct stacks, and let $\lambda : \mathbb{N} \to \Lambda$ be
labels such that for every $i \le m$ the instruction of $M$ at $\lambda(i)$ is stage $i$ of the
drain program for this list and these labels. Then for every state $v$ and stack contents $S$,
the machine runs in exactly $1 + \sum_{i < m} (|S_{k_i}| + 1)$ steps from label $\lambda(0)$,
state $v$ and contents $S$ to the halted configuration whose state stores the flag bit false and
whose contents are empty on each $k_i$ and equal to $S$ on every other stack.
