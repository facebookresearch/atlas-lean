# Tokenizer rejects an undecodable literal

A configuration
$\langle \ell, v \mid x, w, t, b, i, j\rangle$ of the SAT tokenizer has label $\ell$, internal bit
$v$, stacks $X$, $W$, $T$, $B$ holding $x$, $w$, $t$, $b$ (top first; a bit string stands for its
list of bit symbols), and $i$ and $j$ marks on the clause and literal counters. Let $r$ be a bit
string from whose front no literal can be decoded (a literal being a self-delimited canonical
variable code followed by a polarity bit), let $w$, $t$, $b$ be symbol lists,
$i, j \in \mathbb{N}$ and $v$ a bit. Then from
$\langle \mathsf{nm}(\mathrm{none}), v \mid r, w, t, b, i, j\rangle$ the tokenizer reaches the
label $\mathsf{rej}$ within $|r| + 2$ steps.
