# End of a diamond

Let $\varphi$ be a CNF formula with token list $\mathrm{toks}(\varphi)$,
let $y \in \mathbb{N}$ have binary encoding $\mathrm{bin}(y)$, let $\nu$ be a list of symbols and
$b$ a state bit, and let $s$ be a quiescent state of the emitter whose stack $T$ holds
$\mathrm{toks}(\varphi)$ reversed, whose stack $F$ is empty, and whose stack $V$ holds the name of
$y$, then a clause separator, then $\nu$. Let $p, n, r, j, d$ be the values of the counters
$P, N, R, J, D$ of $s$. Then for some state bit $b'$ the emitter goes in exactly
$|\mathrm{toks}(\varphi)| + |\mathrm{bin}(y)| + n + p + r + j + d + 9$ steps from label
$\mathrm{t0}$ with state bit $b$ and the stacks of $s$ to label $\mathrm{h0}$ with state bit $b'$
and the stacks of the quiescent state obtained from $s$ by emptying $T$, setting $F$ to
$\mathrm{toks}(\varphi)$ and $V$ to $\nu$, prepending the reversed name of $y$ to $G$, setting
$P$ to $n + 1$, and setting $N$, $R$, $J$ and $D$ to $0$.
