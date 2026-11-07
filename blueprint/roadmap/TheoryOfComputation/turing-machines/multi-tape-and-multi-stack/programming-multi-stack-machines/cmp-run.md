# Non-destructive comparison of two counters

Let $M$ be a TM2 machine whose state type
carries a flag bit, let $a, b, t_a, t_b$ be pairwise distinct stacks with symbols $u_a$, $u_b$,
$u_{t_a}$, $u_{t_b}$ of their alphabets, let $\ell$ be a label and let $r$, $r'$, $o$ map each
ordering to a label. Suppose that $M$ has at $\ell$ the comparison round of $a$ and $b$ with
scratch stacks $t_a, t_b$ and units $u_{t_a}, u_{t_b}$ that goes to $\ell$ again and exits to
$r(\mathrm{lt})$, $r(\mathrm{eq})$ and $r(\mathrm{gt})$, and that for every ordering $\omega$,
$M$ has at $r(\omega)$ the counter transfer loop of $t_a$ into the single target $(a, u_a)$ that
repeats at $r(\omega)$ and exits to $r'(\omega)$, and has at $r'(\omega)$ the counter transfer
loop of $t_b$ into the single target $(b, u_b)$ that repeats at $r'(\omega)$ and exits to
$o(\omega)$. Write $\mathrm{compare}(m, n)$ for the ordering of natural numbers $m$ and $n$, and
$[m \ne n]$ for $1$ if $m \ne n$ and $0$ otherwise. Then for all $m, n \in \mathbb{N}$, every
state $v$ and all stacks $S$ in which $a$ holds exactly $u_a^m$, $b$ holds exactly $u_b^n$ and
$t_a$ and $t_b$ are empty, $M$ runs in exactly $3\min(m, n) + 3 + [m \ne n]$ steps from label
$\ell$ with state $v$ and stacks $S$ to label $o(\mathrm{compare}(m, n))$ with the state that
stores the flag value false and with the same stacks $S$.
