# Lifting a statement of the second machine

Given finite multi-stack Turing machines
$M_1$ and $M_2$, a statement of $M_2$ is translated into a statement of their composite
machine, whose state is a triple $(v_1, v_2, o)$, by recursion on the statement: an operation
on a stack $k$ of $M_2$ acts on the copy of $k$ among the composite stacks, every read or update
of $M_2$'s state reads or updates the component $v_2$ and leaves $v_1$ and $o$ unchanged, a
branch tests $v_2$, a jump to a label $l$ of $M_2$ becomes a jump to the copy of $l$, and
halting stays halting.
