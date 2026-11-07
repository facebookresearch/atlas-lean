# Stacks during the read loop

For a list $s$ of raw symbols in $\mathrm{Fin}\,r$, a list
$w$ of input codes in $\mathrm{Fin}\,g$, $n \in \mathbb{N}$ and a list $o$ of booleans, these are
the stack contents of the full machine in which the raw-input stack holds $s$, the host input
stack holds $w$, the host output stack holds $o$, the scratch counter $N$ holds $n$ units, and
every other stack is empty.

During the read loop, $s$ is the unread rest of the input and $w$ holds the codes read so far.
