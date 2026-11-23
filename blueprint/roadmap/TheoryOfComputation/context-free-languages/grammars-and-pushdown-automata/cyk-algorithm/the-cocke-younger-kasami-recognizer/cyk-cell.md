# The unshared CYK recurrence

The depth-$n$ CYK cell of a word $w$ is defined by recursion
on $n$: at depth $0$ every cell is empty, and the depth-$(n + 1)$ cell of $w$ is the CYK cell of
$w$ built from the depth-$n$ cells of all words. Cells are recomputed without sharing.
