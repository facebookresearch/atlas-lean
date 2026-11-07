# Number of ones after $t$ steps

For a Busy Beaver machine $M$ and $t \in \mathbb{N}$,
the number of ones of $M$ after $t$ steps is the number of cells $i \in \mathbb{Z}$ with
$-t \le i \le t$ that hold the symbol $1$ in the configuration of $M$ after $t$ steps, started
on the blank tape.

Every one on the tape after $t$ steps lies in this window, since the head moves at most one
cell per step.
