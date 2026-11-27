# Reading the literals of a clause

Let $C$ be a clause with literals
$(n_1, p_1), \dots, (n_k, p_k)$, let $u$ be the concatenation of their literal codes, and let $r$,
$w$ be bit strings, $t$, $b$ stacks of symbols, $c$ a natural number and $v$ a bit. Started at
label $\mathsf{lits}$ with internal bit $v$, the bits of $u$ followed by $r$ on the formula stack
$X$, the bits of $w$ on the witness stack $W$, $t$ on the token stack $T$, $b$ on the table stack
$B$, clause counter $c$ and literal counter $k$, the tokenizer reaches within $2|u| + 1$ steps the
configuration with label $\mathsf{cls}$, internal bit false, the bits of $r$ on $X$, the bits of
$w$ with its first $k$ bits removed on $W$, the tokens of $C$ in reverse order (its final
$\mathsf{cl}$ on top) above $t$ on $T$, the table stack of the entries $e_1, \dots, e_k$ above $b$
on $B$, clause counter $c$ and literal counter $0$. Here $e_i$ pairs the binary name of $n_i$ with
the $i$-th bit of $w$, or with no value when $w$ has fewer than $i$ bits.
