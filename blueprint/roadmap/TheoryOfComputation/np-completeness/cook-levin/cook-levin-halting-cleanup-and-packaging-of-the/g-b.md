# Step bound of the composed machine

Fix the verifier data (an encoding $E$ of a stack
machine $M$, a list $Y$ of input symbols, an output symbol $\mathrm{acc}$, a map $\iota$ into
the input alphabet, a separator $\mathrm{sep}$, a polynomial $k$ and $c, e \in \mathbb{N}$) and an
input length $n$. Let $B(n)$ be the step bound of the full machine on inputs of length $n$, let
$D$ be the depth of the full machine (the most push, peek and pop operations on any path of one
of its instructions), and let $L$ be the number of stacks other than the output stack. The step
bound of the composed machine is $B(n) + 1 + (L(n + B(n) D + 1) + 1)$.
