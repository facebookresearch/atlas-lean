# The diamonds

Let $B \in \mathbb{N}$ and let $\varphi$ be a CNF formula with $m$ clauses,
token list $\mathrm{toks}(\varphi)$ and list of distinct variables $\mathrm{vars}(\varphi)$ of
length $k$. Suppose the top of diamond $k$ for $m$ clauses, the length of $\mathrm{toks}(\varphi)$,
and the length of the binary encoding of every $y \in \mathrm{vars}(\varphi)$ are at most $B$.
Let $\mathrm{vars}(\varphi)$ split as a list $\pi$ followed by a list $u$, let $b$ be a state bit,
and let $s$ be a quiescent state of the emitter such that $T$ and the scratch stack $X$ are empty,
$F$ holds $\mathrm{toks}(\varphi)$, $V$ is the variable stack of $u$, the counter $P$ equals the
top of diamond $|\pi|$, the counter $M$ equals $3m$, the counters $N, R, L, J, D$ are $0$, and the
edge-bit list $q$ is the bits of the arcs of diamonds $0, \dots, |\pi| - 1$ in order, diamond
$i$ taken for the $i$-th entry of $\mathrm{vars}(\varphi)$. Then for some state bit $b'$ and some
stack contents $g'$ the emitter goes in at most $|u|(30B^2 + 100B + 100)$ steps from label
$\mathrm{h0}$ with state bit $b$ and the stacks of $s$ back to label $\mathrm{h0}$ with state bit
$b'$ and the stacks of $s$ changed as follows: $V$ becomes empty, $P$ becomes the top of diamond
$k$, $q$ becomes the bits of all arcs of the construction for $\varphi$, and $G$ becomes $g'$.
