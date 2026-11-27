# Multi-target transfer

Let $M$ be a counter machine with counters indexed by $C$, a
Boolean output stack and a Boolean state, let $x \in C$, and let $Y$ be a list of distinct
counters not containing $x$. Suppose the instruction at label $\ell$ is the transfer loop that
pops counter $x$ and pushes one unit on every counter of $Y$, returning to $\ell$ while $x$ is
nonempty and continuing at label $\ell'$ once it is empty. Then for all counter values
$F : C \to \mathbb{N}$, every state bit $v$ and every output stack $o$, the machine runs in
exactly $F(x) + 1$ steps from label $\ell$ with state $v$, counter values $F$ and output stack $o$
to label $\ell'$ with state false, output stack $o$ and the counter values after transferring
$x$ to $Y$: counter $x$ becomes $0$, each counter of $Y$ gains $F(x)$, and every other counter
keeps its value.
