# The CLIQUE emitter computes Karp's instance in cubic time

Let $\varphi$ be a CNF formula
with token list $\tau$ (in reading order), $o$ a list of Booleans, $v$ a flag, and $S$ stack
contents in which the token stack $T$ holds $\tau$ reversed (stacks are listed top first), the
output stack $O$ holds $o$ and every other stack is empty. Started at its start label with flag
$v$ and stacks $S$, the CLIQUE emitter reaches the label $\mathrm{done}$ in at most
$8(|\tau| + 1)^3$ steps, with some flag and stacks $S'$ such that $O$ holds, in $S'$, Karp's
CLIQUE instance of $\varphi$ followed by $o$.
