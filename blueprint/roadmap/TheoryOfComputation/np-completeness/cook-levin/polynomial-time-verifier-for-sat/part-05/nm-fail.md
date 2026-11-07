# Rejecting an unterminated name block

Let $r$ be a bit string from whose front no
self-delimiting block can be parsed. For every optional last bit $\ell$, internal bit $v$, symbol
stacks $w$, $t$, $b$ and natural numbers $c$, $l$, the tokenizer started at label
$\mathsf{nm}(\ell)$ with internal bit $v$, the bits of $r$ on the formula stack $X$, $w$ on the
witness stack $W$, $t$ on the token stack $T$, $b$ on the table stack $B$, clause counter $c$ and
literal counter $l$ reaches the label $\mathsf{rej}$ within $|r| + 1$ steps.
