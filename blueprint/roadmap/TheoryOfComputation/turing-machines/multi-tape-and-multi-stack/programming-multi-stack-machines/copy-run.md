# Copying a counter through a scratch stack

Let $a, c, t$ be pairwise distinct stacks with
unit symbols $u_a, u_c, u_t$. Write $\mathrm{xfer}(k, ps, \ell, \ell')$ for the transfer loop at
label $\ell$ that pops stack $k$ until it is empty, pushing $x$ onto stack $j$ for each pair
$(j, x)$ in $ps$ per popped symbol, and then goes to $\ell'$. Suppose the machine $M$ has
$M(l_1) = \mathrm{xfer}(a, [(c, u_c), (t, u_t)], l_1, l_2)$ and
$M(l_2) = \mathrm{xfer}(t, [(a, u_a)], l_2, \mathit{next})$. Let $m, p \in \mathbb{N}$, let $v$
be a state and let $S$ be stacks in which $a$ holds exactly $u_a^m$, $c$ holds $u_c^p$ and $t$ is
empty. Then exactly $2m + 2$ steps of $M$ lead from label $l_1$ with state $v$ and stacks $S$ to
label $\mathit{next}$ with the state storing the flag false and the stacks $S$ with $c$ replaced
by $u_c^{m+p}$.
