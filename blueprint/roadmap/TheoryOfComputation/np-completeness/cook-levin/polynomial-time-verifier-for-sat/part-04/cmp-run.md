# Serving a live table entry

Write stack contents top first, and for a list of bits $u$ let
$\overrightarrow{u}$ be its bit symbols in order and $\overleftarrow{u}$ the same symbols in
reverse order. Let $q$ and $n$ be lists of bits, $b$ and $x$ bits, $s$ a list of symbols, and $R$,
$r$ lists of symbols each empty or topped by a symbol that is not a bit. From label
$\mathsf{cmp}(b)$ with any internal state, $\overleftarrow{q}R$ on $T$, $\overleftarrow{n}r$ on
$B$, $s$ on $S$, the stacks $A$ and $C$ empty and the bit symbol of $x$ alone on $V$, the lookup
program reaches, in at most $4|n| + 5$ steps, label $\mathsf{scan}$ with some internal state,
$\overleftarrow{q}R$ on $T$, $r$ on $B$, $\overrightarrow{n}s$ on $S$, the stacks $A$ and $C$
empty and on $V$ alone the bit symbol of $b$ if $n = q$ and of $x$ otherwise.
