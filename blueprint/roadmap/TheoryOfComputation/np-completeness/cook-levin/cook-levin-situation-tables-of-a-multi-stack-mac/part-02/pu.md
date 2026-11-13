# Pushed-symbol table of a situation

Fix an encoding record $E$ of a finite multi-stack
machine. For a situation $i$, a stack number $k$ and a depth $j$, $\mathrm{pu}(i, k, j)$ is the
code of the symbol at position $j$ from the top (counting from $0$) among the symbols that the
effect of situation $i$ leaves pushed on the stack that the inverse stack numbering of $E$ assigns
to $k$, and $0$ if fewer than $j + 1$ symbols are left pushed there.
