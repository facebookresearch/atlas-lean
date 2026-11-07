# Tokenizer rejects undecodable literals

A configuration
$\langle \ell, v \mid x, w, t, b, i, j\rangle$ of the SAT tokenizer has label $\ell$, internal bit
$v$, stacks $X$, $W$, $T$, $B$ holding $x$, $w$, $t$, $b$ (top first; a bit string stands for its
list of bit symbols), and $i$ and $j$ marks on the clause and literal counters. Let
$c, k \in \mathbb{N}$, let $r$ and $w$ be bit strings, $t$ and $b$ symbol lists and $v$ a bit, and
suppose that decoding $k$ literals from the front of $r$ fails. Then from
$\langle \mathsf{lits}, v \mid r, w, t, b, c, k\rangle$ the tokenizer reaches the label
$\mathsf{rej}$ within $2|r| + 3$ steps.
