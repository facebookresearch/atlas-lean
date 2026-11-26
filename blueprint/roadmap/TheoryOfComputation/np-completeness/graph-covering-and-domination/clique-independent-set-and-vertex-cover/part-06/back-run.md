# Clique emitter: moving the walk side back

Let $p$ and $v$ be Booleans, $t$, $a$ and $d$
stack-symbol lists, $o$ a list of bits, $c, n \in \mathbb{N}$, and let $L$ be a list of stack
symbols each of which is a name bit, a polarity marker or a clause marker. From label
$\mathrm{back}(p)$ with flag $v$ and the state with token stack $t$, output $o$, name stack $a$,
walked stack $d$, walk side $L$, clause count $c$, occurrence count $n$ and empty scratch stacks,
the emitter machine reaches in exactly $|L| + 1$ steps, for some flag $v'$, label
$\mathrm{put}(p)$ with flag $v'$ and the same state except that the walked stack is the reverse
of $L$ followed by $d$ and the walk side is empty.
