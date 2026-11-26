# Cleanup empties its stacks

Let $ks$ be a list of pairwise distinct stacks of a program
$M$ whose state carries a flag bit, and $\mathit{self}$, $\mathit{next}$ labels such that $M$
runs at $\mathit{self}$ the cleanup round for $ks$, looping at $\mathit{self}$ and exiting to
$\mathit{next}$. Let $m$ be a natural number and $S$ stack contents in which every stack of $ks$
holds at most $m$ symbols. Then for every state $v$, $M$ runs in at most $m + 1$ steps from label
$\mathit{self}$, state $v$ and stacks $S$ to label $\mathit{next}$, the state storing the flag
value false, and the stacks $S'$ with $S'(k)$ empty for every $k$ in $ks$ and $S'(k) = S(k)$ for
every other stack $k$.
