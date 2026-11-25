# Adding a canonical chosen block

Let $p$ and $\mathit{rest}$ be bit lists and $z$ a bit
such that $p$ is nonempty and ends in true, or $p$ is empty and $z$ is false (the flag $z$
records whether the bits of the block read so far end in false), and let $c$ be a bit. Start the
SUBSET-SUM verifier machine at the label that adds a chosen number with carry $c$ and flag $z$,
with any value of the local variable, the self-delimiting encoding of $p$ followed by
$\mathit{rest}$ (as bit symbols) on the input stack $X$, symbol lists $w$ on $W$ and $t$ on $T$, a
bit list $u$ (as bit symbols, least significant bit first) on the sum stack $A$, a symbol list
$\mathit{acc}$ on $B$, and the scratch stacks $P$ and $Q$ empty. Then within $|p| + |u| + 2$ steps
the machine reaches the label that moves the new sum back, with some value of the local variable,
$\mathit{rest}$ on $X$, $w$ on $W$, $t$ on $T$, $A$, $P$ and $Q$ empty, and on $B$ the ripple-carry
sum of $u$ and $p$ with carry-in $c$ (as bit symbols, most significant bit on top) above
$\mathit{acc}$.
