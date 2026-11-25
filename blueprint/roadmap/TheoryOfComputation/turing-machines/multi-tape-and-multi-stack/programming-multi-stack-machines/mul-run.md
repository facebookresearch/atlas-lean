# Multiplying unary counters

Let $M$ be a multi-stack machine whose states carry a flag
bit, with $\mathrm{tag}(\mathrm{false})$ the state storing the bit false; write $(\ell, v, S)$ for
the configuration at label $\ell$ with state $v$ and stack contents $S$, and $u^m$ for a stack
holding exactly $m$ copies of the symbol $u$. Let $a, a', b, c, t$ be pairwise distinct stacks
with symbols $u_a, u_{a'}, u_b, u_c, u_t$ of the respective stacks, and let $h, \ell_1, \ell_2, r,
e$ be labels such that: at $h$ the machine runs the loop head on $a$ with index stack $a'$ (pop
$a$; if a symbol was popped, push $u_{a'}$ onto $a'$ and go to $\ell_1$, otherwise go to $r$); at
$\ell_1$ it runs the transfer that drains $b$, pushing $u_c$ onto $c$ and $u_t$ onto $t$ per
popped symbol, and then goes to $\ell_2$; at $\ell_2$ it runs the transfer that drains $t$,
pushing $u_b$ onto $b$ per popped symbol, and then goes to $h$; and at $r$ it runs the transfer
that drains $a'$, pushing $u_a$ onto $a$ per popped symbol, and then goes to $e$. Then for all
$m, n, p \in \mathbb{N}$, every state $v$ and all stack contents $S$ with $S_a = u_a^m$, $S_{a'}$
empty, $S_b = u_b^n$, $S_c = u_c^p$ and $S_t$ empty, $M$ goes from $(h, v, S)$ to
$(e, \mathrm{tag}(\mathrm{false}), S')$ in exactly $m(2n + 3) + m + 2$ steps, where $S'$ agrees
with $S$ on every stack except $c$ and $S'_c = u_c^{mn + p}$.
