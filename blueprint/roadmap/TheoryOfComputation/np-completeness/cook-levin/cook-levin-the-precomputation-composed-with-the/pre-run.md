# The precomputation

Fix the full program built from a code map $c_f$ from the raw alphabet
$\mathrm{Fin}\,r$ to the code alphabet $\mathrm{Fin}\,g$, a separator code $c_s$, a polynomial $k$
with natural coefficients, constants $c, e, d \in \mathbb{N}$, a host program and its start label.
Let $s = s_1 \cdots s_n$ be a raw input word and $o$ a list of booleans. Started at the read-loop
label with flag false, raw input stack $s$, output stack $o$ and every other stack empty, the full
program reaches the host's start label with flag false within $n + 1 + B + 1$ steps, where $B$ is
the counter program's step budget for $k, c, e, d$ at $n$. The stacks it reaches satisfy: the
output stack is still $o$; the input stack is $c_s, c_f(s_n), \dots, c_f(s_1)$; for every target
$y$, the host counter receiving $y$ has length equal to the target value of $y$ for $k, c, e, d$
at $n$; and every host stack other than the output stack, the input stack and the host counters
receiving targets is empty.

These are the preloads that the assembled generator's run expects.
