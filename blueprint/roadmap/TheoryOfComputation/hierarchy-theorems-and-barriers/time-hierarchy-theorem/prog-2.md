# Program of the layout machine

Writing $1$ for true and $0$ for false, this is the
program of a multi-stack machine whose stacks $X, Z, P, P_2, U, N, A_2, B_2, D, C, T, O$ all hold
bits. To move a stack $S$ onto a stack $S'$ means to pop the bits of $S$ one at a time, pushing
each onto $S'$, until $S$ is empty; to transfer $S$ to some stacks means to pop $S$ until it is
empty, pushing a $1$ on each of these stacks for every bit popped. From the label $\mathsf{s0}$
the program pops $X$. If $X$ was empty or the popped bit is $0$, it pushes $0, 0, 1, 1, 0$ on $O$
in this order and halts. Otherwise it moves $X$ onto $Z$, and then, as long as $Z$ is nonempty,
it pops a bit $b$ from $Z$, pushes $b$ on $U$ and a $1$ on $N$, and pushes $0, 1, 1$ on $P$ in
this order if $b = 1$ and $0, 1$ if $b = 0$. Then it moves $U$ onto $O$, pushes a $0$ on $O$,
moves $P$ onto $P_2$ and then $P_2$ onto $O$, and transfers $N$ to $A_2$ and $B_2$. Then it
loops: it pops $A_2$; if a bit was popped, it pushes a $1$ on $D$, transfers $B_2$ to $C$ and
$T$, transfers $T$ to $B_2$ and loops again; if $A_2$ was empty, it transfers $D$ to $A_2$.
Finally it pushes $0, 1$ on $O$ in this order, transfers $C$ to $O$ and halts.
