# Appending one more gate keeps the earlier gate values

Let $p$ be a program with $g$
gates over $m$ inputs, let $c \in \mathbb{N}$, and for each $j \le c$ let $f_j$ be a line that
reads the inputs and the first $g + j$ gates. Under any interpretation of the gate symbols and
any input values, for every $k < g + c$ the value of gate $k$ of the program obtained by
appending $f_0, \dots, f_c$ to $p$ equals the value of gate $k$ of the program obtained by
appending $f_0, \dots, f_{c-1}$ to $p$ (no gates when $c = 0$).
