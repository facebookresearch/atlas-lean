# Hopcroft's refinement loop

Let $M$ be a DFA. Given a round budget $k$, a partition $P$
of the states of $M$ (a list of blocks) and a waiting list $W$ of splitters $(C, a)$, each a block
$C$ with a letter $a$, the loop returns the pair $(P, W)$ unchanged if $k = 0$ or $W$ is empty.
Otherwise it removes the first splitter $(C, a)$ from $W$, replaces $P$ by the partition after the
splitter $(C, a)$ and the remaining waiting list by the waiting list after the splitter $(C, a)$,
and continues with budget $k - 1$.
