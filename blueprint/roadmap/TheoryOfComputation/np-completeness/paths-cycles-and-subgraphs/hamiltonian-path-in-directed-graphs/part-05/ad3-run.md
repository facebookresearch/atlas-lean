# HAMPATH emitter, phase A: copying a reversed name onto two stacks

Let $u$ be a list of
bits and let $s$ be a quiescent state of the HAMPATH emitter whose stack $X$ holds $u$ as
name-bit symbols. Then for every value $v$ of the machine's Boolean variable there is a value
$v'$ such that the emitter goes in exactly $|u| + 1$ steps from label $\mathrm{ad3}$, variable
$v$ and the stacks of $s$ to label $\mathrm{a0}$, variable $v'$ and the stacks of the state
obtained from $s$ by emptying $X$ and replacing each of $F$ and $V$ by the reverse of $u$ (as
name-bit symbols) followed by its old contents.
