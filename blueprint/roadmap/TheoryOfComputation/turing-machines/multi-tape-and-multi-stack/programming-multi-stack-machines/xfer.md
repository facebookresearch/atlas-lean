# Counter transfer loop

For a multi-stack machine whose internal state carries a flag bit, a stack $k$, a list $ps$ of
pairs $(t, x)$ of a stack $t$ and a symbol $x$ of stack $t$, and labels $\ell$ and $\ell'$, this
machine statement pops stack $k$, stores in the flag whether a symbol was popped, and branches on
it: if a symbol was popped, it pushes $x$ onto $t$ for each pair $(t, x)$ of $ps$ in list order
and goes to $\ell$; if stack $k$ was empty, it goes to $\ell'$. No condition is imposed on $ps$:
a stack may occur several times as a target, and $k$ itself may be a target.

Placed at its own label $\ell$, the statement is a loop. When $k$ is not one of the target stacks,
each round removes one symbol from $k$, so a stack $k$ holding $n$ symbols is emptied after $n$
rounds and the loop exits to $\ell'$ in the next step, having pushed $n$ copies of $x$ onto $t$ for
every pair $(t, x)$ of $ps$, on top of the previous contents of $t$ (see
[running a counter transfer](xfer-run.md),
which also assumes that the target stacks are pairwise distinct and that $k$ holds $n$ copies of
one symbol). If $k$ is itself a target, a popped symbol can be pushed straight back onto $k$:
for instance with $ps = [(k, u)]$ and $k$ holding one $u$, the loop never empties $k$ and never
exits. Thus, for $k$ not a target: with $ps$ empty the loop drains $k$; with one target stack that
is initially empty it moves the counter of $k$ there; and with two distinct target stacks that are
initially empty it copies the counter to both.
