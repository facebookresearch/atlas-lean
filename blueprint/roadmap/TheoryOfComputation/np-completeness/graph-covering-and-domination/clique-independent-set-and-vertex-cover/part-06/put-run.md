# CLIQUE emitter: putting the current occurrence on the walked stack

Stacks are listed top
first. Let $p$ be a Boolean, $u$ a list of Booleans and $\bar u$ the list of bit symbols
$\mathrm{bit}(b)$ for $b$ in $u$, let $v$ be a flag, $t$, $d$, $e$ lists of symbols, $o$ a list of
Booleans and $c, n \in \mathbb{N}$. Started at label $\mathrm{put}(p)$ with flag $v$, stacks $T$,
$O$, $A$, $D$, $E$ holding $t$, $o$, $\bar u$, $d$, $e$, empty scratch stacks $B$ and $X$, and $c$
and $n$ clause markers on the counters $C$ and $N$, the CLIQUE emitter reaches, in exactly
$2|u| + 3$ steps and with some flag, the label $\mathrm{lits}$ with $A$ empty, $D$ holding the
literal marker $\mathrm{lit}(p)$ on top of $\bar u$ on top of $d$, and all other stacks as before.

The name goes from $A$ to $D$ through $B$, so it is reversed twice.
