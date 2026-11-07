# The reduction machine

Fix $r \in \mathbb{N}$, a finite TM2 machine $M$ with an encoding
$E$, a list $Y$ of input symbols of $M$, an output symbol $a$, a map $\iota$ from
$\{0, \dots, r-1\}$ to input symbols, an input symbol $\mathit{sep}$, a polynomial $k$ with
coefficients in $\mathbb{N}$ and $c, e \in \mathbb{N}$. The reduction machine is the finite TM2
machine with the stacks and alphabets of the full machine, input on the raw-input stack and
output on the output stack; its labels are those of the full machine together with the drain
stages $0, \dots, n$, where $n$ is the number of stacks other than the output stack; it starts at
the read-loop label with state false; and its program is the composed program of the full
machine's program and its final label: the full machine, followed by the drain.
