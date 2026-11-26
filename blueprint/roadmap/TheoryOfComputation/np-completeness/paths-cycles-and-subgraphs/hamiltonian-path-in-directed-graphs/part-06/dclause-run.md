# One clause of the detour walk

Let $B, m, i, y, j \in \mathbb{N}$, let $C$ be a clause
with token list $\mathrm{toks}(C)$, let $\rho$ and $\nu$ be lists of symbols and $b$ a state bit,
and let $s$ be a quiescent state of the emitter such that $F$ holds $\mathrm{toks}(C)$ followed by
$\rho$, $V$ holds the name of $y$, then a clause separator, then $\nu$, the scratch stack $X$ is
empty, the counter $J$ equals $j$, the counter $D$ equals row vertex $3j + 1$ of diamond $i$ for
$m$ clauses, each of the counters $P, N, R, J, D$ is at most $B$, and the binary encoding of $y$
has length at most $B$. Then for some state bit $b'$ the emitter goes in at most
$|\mathrm{toks}(C)|(3B + 6) + 16B + 26$ steps from the detour-walk label with both clause flags
false, state bit $b$ and the stacks of $s$ back to the same label with state bit $b'$ and the
stacks of $s$ changed as follows: $F$ becomes $\rho$, $\mathrm{toks}(C)$ reversed is prepended to
$T$, $J$ becomes $j + 1$, $D$ increases by $3$, and the edge-bit list $q$ is extended by the bits
of the detour arcs of clause $j$ (contents $C$) in diamond $i$ for variable $y$.
