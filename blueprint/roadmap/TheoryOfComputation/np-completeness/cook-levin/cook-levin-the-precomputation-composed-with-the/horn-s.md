# The statements of one Horner round

For counters $b, \mathit{acc}, q, d, t$, a number
$a \in \mathbb{N}$, stage labels $\mu$ and an exit label $\nu$: the statements performing
$\mathit{acc} \leftarrow \mathit{acc} \cdot b + a$ in four stages, each stage reaching the next
through $\mu$. The multiplication stages add $\mathit{acc} \cdot b$ to $q$ (with index counter $d$
and scratch counter $t$), then the drain stage empties $\mathit{acc}$, the move stage transfers
$q$ into $\mathit{acc}$, and the add stage pushes $a$ units onto $\mathit{acc}$ and continues at
$\nu$.
