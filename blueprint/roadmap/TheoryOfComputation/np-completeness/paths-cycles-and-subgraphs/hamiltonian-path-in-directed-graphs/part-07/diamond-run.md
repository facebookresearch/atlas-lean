# One diamond

Let $B, i, y \in \mathbb{N}$, let $u$ be a list of natural numbers, let
$\varphi$ be a CNF formula with $m$ clauses and token list $\mathrm{toks}(\varphi)$, let $b$ be a
state bit, and let $s$ be a quiescent state of the emitter such that $T$ and the scratch stack $X$
are empty, $F$ holds $\mathrm{toks}(\varphi)$, $V$ is the variable stack of the list $y$ followed
by $u$, the counter $P$ equals the top of diamond $i$ for $m$ clauses, the counter $M$ equals
$3m$, the counters $N, R, L, J, D$ are $0$, and $B$ bounds the top of diamond $i + 1$, the length
of the binary encoding of $y$, and the length of $\mathrm{toks}(\varphi)$. Then for some state bit
$b'$ the emitter goes in at most $30B^2 + 100B + 100$ steps from label $\mathrm{h0}$ with state
bit $b$ and the stacks of $s$ back to label $\mathrm{h0}$ with state bit $b'$ and the stacks of
$s$ changed as follows: $V$ becomes the variable stack of $u$, $P$ becomes the top of diamond
$i + 1$, the edge-bit list $q$ is extended by the bits of the arcs of diamond $i$ of $\varphi$ for
variable $y$, and the reversed name of $y$ is prepended to $G$.
