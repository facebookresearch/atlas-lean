# Tokenizer rejects undecodable clauses

A configuration
$\langle \ell, v \mid x, w, t, b, i, j\rangle$ of the SAT tokenizer has label $\ell$, internal bit
$v$, stacks $X$, $W$, $T$, $B$ holding $x$, $w$, $t$, $b$ (top first; a bit string stands for its
list of bit symbols), and $i$ and $j$ marks on the clause and literal counters. Let
$n \in \mathbb{N}$, let $r$ and $w$ be bit strings, $t$ and $b$ symbol lists and $v$ a bit, and
suppose that decoding $n$ clauses (each a unary literal count followed by that many encoded
literals) from the front of $r$ fails. Then from
$\langle \mathsf{cls}, v \mid r, w, t, b, n, 0\rangle$ the tokenizer reaches the label
$\mathsf{rej}$ within $2|r| + n + 2$ steps.
