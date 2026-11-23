# Gap emission

Let $P, Q, T_1, T_2, o$ be pairwise distinct stacks, with unit symbols
$u_P, u_Q, u_{T_1}, u_{T_2}$ for the first four, and let $ys$ be a list of symbols of stack $o$.
Write $\mathrm{xfer}(k, ps, \ell, \ell')$ for the transfer loop at label $\ell$ that pops stack
$k$ until it is empty, pushing $x$ onto stack $j$ for each pair $(j, x)$ in $ps$ per popped
symbol, and then goes to $\ell'$. Let $r, r_B, \mathit{out}$ map each ordering to a label, with
$\mathit{out}(\mathrm{eq}) = \mathit{next}$ and $\mathit{out}(\omega) = \mathit{emit}$ for every
ordering $\omega \ne \mathrm{eq}$. Suppose the machine $M$ has: at label $\mathit{dec}$ the
decrement of $P$ that goes to $\mathit{cmp}$ if a symbol was popped and to $\mathit{ifZero}$ if
$P$ was empty; at label $\mathit{cmp}$ the comparison round of $P$ and $Q$ with scratch stacks
$T_1, T_2$ and units $u_{T_1}, u_{T_2}$ that repeats at $\mathit{cmp}$ and exits to
$r(\mathrm{lt})$, $r(\mathrm{eq})$ and $r(\mathrm{gt})$; for every ordering $\omega$,
$M(r(\omega)) = \mathrm{xfer}(T_1, [(P, u_P)], r(\omega), r_B(\omega))$ and
$M(r_B(\omega)) = \mathrm{xfer}(T_2, [(Q, u_Q)], r_B(\omega), \mathit{out}(\omega))$; and at
label $\mathit{emit}$ the statement that prepends $ys$ to stack $o$ (so that $ys$ reads top-down)
and goes to $\mathit{dec}$. Let $q \in \mathbb{N}$. Then for every $g \in \mathbb{N}$, every
state $v$ and all stacks $S$ in which $P$ holds exactly $u_P^{q+g+1}$, $Q$ holds $u_Q^q$, and
$T_1$ and $T_2$ are empty, exactly $g(3q + 6) + 3q + 4$ steps of $M$ lead from label
$\mathit{dec}$ with state $v$ and stacks $S$ to label $\mathit{next}$ with the state storing the
flag false and the stacks $S$ with $P$ replaced by $u_P^q$ and $o$ replaced by $g$ copies of $ys$
concatenated, followed by the old contents of $o$.
