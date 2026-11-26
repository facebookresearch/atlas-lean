# Lifting a statement of the first machine

Given finite multi-stack Turing machines
$M_1$ and $M_2$, a statement of $M_1$ is translated into a statement of their composite
machine, whose state is a triple $(v_1, v_2, o)$, by recursion on the statement: an operation
on a stack $k$ of $M_1$ acts on the copy of $k$ among the composite stacks, every read or update
of $M_1$'s state reads or updates the component $v_1$ and leaves $v_2$ and $o$ unchanged, a
branch tests $v_1$, a jump to a label $l$ of $M_1$ becomes a jump to the copy of $l$, and
halting becomes a jump to the pop label of the first copy loop, which moves $M_1$'s output.
