# The full machine as a finite multi-stack Turing machine

Given $r \in \mathbb{N}$, an
encoding $E$ of the machine $M$, a list $Y_s$ of input symbols of $M$, an output symbol $a$ of
$M$, a map $\iota$ from $\{0, \dots, r - 1\}$ to input symbols of $M$, an input symbol $\sigma$ of
$M$ (the separator), a polynomial $k$ with natural coefficients and $c, e \in \mathbb{N}$: the
finite multi-stack machine whose stacks are the full stacks (the host's stacks, the raw input
stack and the scratch counters) with the full alphabets, whose labels are the full labels, with
start label the read label, internal states the booleans with initial state false, and program
the full program built from these data. Its input stack is the raw input stack and its output
stack is the host's output stack.
