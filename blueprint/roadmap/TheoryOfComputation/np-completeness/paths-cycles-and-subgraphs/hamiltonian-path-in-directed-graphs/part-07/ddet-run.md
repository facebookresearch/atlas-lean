# The detours of a diamond

Let $B, i, y \in \mathbb{N}$, let $\varphi$ be a CNF formula
with $m$ clauses and token list $\mathrm{toks}(\varphi)$, let $\nu$ be a list of symbols and $b$
a state bit, and let $s$ be a quiescent state of the emitter such that $F$ holds
$\mathrm{toks}(\varphi)$, $T$ and the scratch stack $X$ are empty, $V$ holds the name of $y$, then
a clause separator, then $\nu$, the counter $P$ equals the top of diamond $i$ for $m$ clauses, the
counters $J$ and $D$ are $0$, the counters $N$ and $R$ are at most $B$, the binary encoding of $y$
has length at most $B$, and row vertex $3m$ of diamond $i$ is at most $B$. Then for some state bit
$b'$ the emitter goes in at most
$|\mathrm{toks}(\varphi)|(3B + 6) + m(16B + 26) + 2B + 5$ steps from label $\mathrm{e0}$ with state
bit $b$ and the stacks of $s$ to label $\mathrm{t0}$ with state bit $b'$ and the stacks of $s$
changed as follows: $F$ becomes empty, $T$ becomes $\mathrm{toks}(\varphi)$ reversed, $J$ becomes
$m$, $D$ becomes row vertex $3m + 1$ of diamond $i$, and the edge-bit list $q$ is extended by the
bits of the detour arcs, for $j = 0, \dots, m - 1$ in order, of clause $j$ of $\varphi$ in diamond
$i$ for variable $y$.
