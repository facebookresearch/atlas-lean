# Program of the checking machine

Writing $1$ for true and $0$ for false, this is the
program of a multi-stack machine whose stacks $X, Y, W, V, Q, A, P_Q, P_A, T_1, T_2, J, O$ all
hold bits. To read a cell from $V$ onto a stack $S$ means to pop the leading $1$s of $V$, pushing
a $1$ on $S$ for each, and then to pop the $0$ that follows; if $V$ is empty at that point, the
machine rejects. From its first label the program pops the bits of $X$ one at a time, pushing
each onto both $Y$ and $W$, and then pops the bits of $W$ one at a time onto $V$. Then it loops.
If $V$ is empty, it pops the bits of $Y$ one at a time onto $O$, pushes a $1$ on $O$ and halts.
Otherwise it reads a cell from $V$ onto $Q$ and then one onto $A$. With $p_Q$, $q$, $p_A$, $a$
the numbers of bits on $P_Q$, $Q$, $P_A$, $A$, it compares $p_Q$ with $q$ and, if they are
equal, $p_A$ with $a$, afterwards pushing back as many $1$s as it popped from each. If
$p_Q > q$, or $p_Q = q$ and $p_A > a$, it rejects; otherwise it reads two more cells from $V$
onto $J$, empties $P_Q$ and $P_A$, moves $Q$ onto $P_Q$ and $A$ onto $P_A$ (pushing a $1$ for
each bit popped), pushes one more $1$ on $P_A$ and loops again. Rejecting pushes a single $0$ on
$O$ and halts.
