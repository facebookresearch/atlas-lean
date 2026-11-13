# The cell view of an input tape

For every word $w = w_0 w_1 \cdots w_{n-1}$ over $\Gamma$,
the cell view of the input tape of $w$ is the Mathlib input tape of the list of non-blank cells
$w_0, \dots, w_{n-1}$: the head is on $w_0$, the letters $w_1, \dots, w_{n-1}$ lie to its right
in order, and every other cell is blank (for the empty word, every cell is blank).
