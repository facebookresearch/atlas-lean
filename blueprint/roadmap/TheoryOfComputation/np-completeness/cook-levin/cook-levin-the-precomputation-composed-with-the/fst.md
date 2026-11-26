# Stacks during the read loop

For a list $s$ of raw symbols in $\{0, \dots, r - 1\}$, a list
$w$ of input codes in $\{0, \dots, g - 1\}$, $n \in \mathbb{N}$ and a list $o$ of booleans, these are
the stack contents of the full machine in which the raw-input stack holds $s$, the host input
stack holds $w$, the host output stack holds $o$, the scratch counter $N$ holds $n$ units, and
every other stack is empty.

During the read loop, $s$ is the unread rest of the input and $w$ holds the codes read so far.
