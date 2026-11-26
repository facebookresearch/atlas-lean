# Reading a name block

Let $u$ and $r$ be bit strings, $\ell$ an optional bit, $v$ a bit,
$w$, $t$, $b$ symbol stacks and $c$, $l$ natural numbers. Started at label $\mathsf{nm}(\ell)$ with
internal bit $v$, the bits of the self-delimiting block of $u$ followed by $r$ on the formula stack
$X$, $w$ on the witness stack $W$, $t$ on the token stack $T$, $b$ on the table stack $B$, clause
counter $c$ and literal counter $l$, the tokenizer runs in exactly $|u| + 1$ steps to the
configuration whose label is the name-loop outcome for $\ell$ and $u$, with internal bit true, the
bits of $r$ on $X$, $w$ on $W$, the bits of $u$ in reverse order (last bit on top) above $t$ on $T$
and above $b$ on $B$, and the same counters.
