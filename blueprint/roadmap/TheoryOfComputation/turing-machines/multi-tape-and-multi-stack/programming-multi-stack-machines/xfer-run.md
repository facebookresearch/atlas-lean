# Running a counter transfer

Let $M$ be a multi-stack machine whose state carries a
flag bit, and suppose that at label $\ell$ it executes the transfer loop that empties stack $k$
into the targets $p_1, \dots, p_m$ and then goes to label $\ell'$. Here each target $p_i$ is a
pair of a stack $t_i$ and a symbol $x_i$ of its alphabet, the stacks $t_1, \dots, t_m$ are
distinct, and $k$ is none of them. Let $u$ be a symbol of stack $k$. Then for every $n$, every
state $v$ and all stack contents $S$ in which stack $k$ holds exactly $u^n$, the machine goes in
exactly $n + 1$ steps from label $\ell$ with state $v$ and stacks $S$ to label $\ell'$ with the
state that stores the flag value false and the stacks obtained from $S$ by emptying stack $k$
and then pushing $n$ copies of $x_i$ on each stack $t_i$.
