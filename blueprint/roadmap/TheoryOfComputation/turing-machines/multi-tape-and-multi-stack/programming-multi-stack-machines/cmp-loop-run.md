# The comparison loop

Let $a, b, t_a, t_b$ be pairwise distinct stacks with unit symbols
$u_a, u_b, u_{t_a}, u_{t_b}$, and let $r$ map each ordering to a label. Suppose the machine $M$
has at label $\ell$ the comparison round of $a$ and $b$ with scratch stacks $t_a, t_b$ and units
$u_{t_a}, u_{t_b}$ that repeats at $\ell$ and exits to $r(\mathrm{lt})$, $r(\mathrm{eq})$ and
$r(\mathrm{gt})$: it pops $a$ and $b$, pushes $u_{t_a}$ onto $t_a$ if $a$ was non-empty and
$u_{t_b}$ onto $t_b$ if $b$ was non-empty, and goes to $\ell$ if both were non-empty, to
$r(\mathrm{lt})$ if only $b$ was, to $r(\mathrm{eq})$ if neither was and to $r(\mathrm{gt})$ if
only $a$ was. Then for all $m, n, p, q \in \mathbb{N}$, every state $v$ and all stacks $S$ in
which $a, b, t_a, t_b$ hold exactly $u_a^m, u_b^n, u_{t_a}^p, u_{t_b}^q$ respectively, there are
a state $v'$ and stacks $S'$ such that exactly $\min(m, n) + 1$ steps of $M$ lead from label
$\ell$ with state $v$ and stacks $S$ to label $r(\mathrm{compare}(m, n))$ with state $v'$ and
stacks $S'$, where in $S'$ the stack $a$ holds $u_a^{m - \min(m, n+1)}$, $b$ holds
$u_b^{n - \min(n, m+1)}$, $t_a$ holds $u_{t_a}^{p + \min(m, n+1)}$, $t_b$ holds
$u_{t_b}^{q + \min(n, m+1)}$, and every other stack is as in $S$.
