# Appending a block of gates

Let $p$ be a straight-line program with $g$ gates over $m$
inputs, let $c \in \mathbb{N}$, and for each $j < c$ let $f_j$ be a line (a gate operation with
its argument wires) that reads the inputs and the first $g + j$ gates. Appending
$f_0, \dots, f_{c-1}$ to $p$ gives the program with $g + c$ gates whose first $g$ gates are
those of $p$ and whose gate $g + j$ is $f_j$ for each $j < c$. It is defined by recursion on
$c$, adding one gate at a time.
