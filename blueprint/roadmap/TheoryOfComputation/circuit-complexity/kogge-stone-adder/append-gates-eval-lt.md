# Appending gates keeps the old gate values

Let $p$ be a program with $g$ gates over $m$
inputs, let $c \in \mathbb{N}$, and for each $j < c$ let $f_j$ be a line that reads the inputs
and the first $g + j$ gates. Under any interpretation of the gate symbols and any input values,
for every $k < g$ the value of gate $k$ of the program obtained by appending
$f_0, \dots, f_{c-1}$ to $p$ equals the value of gate $k$ of $p$.
