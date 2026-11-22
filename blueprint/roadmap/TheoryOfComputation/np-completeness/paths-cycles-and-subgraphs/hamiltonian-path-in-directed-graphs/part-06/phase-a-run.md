# Phase A of the HAMPATH emitter

Let $\varphi$ be a CNF formula with $m$ clauses whose token
list has length $L$, let $o$ be a list of bits and let $v$ be a bit. Started at label
$\mathrm{a0}$ with internal state $v$ and the stacks of the initial emitter state of $\varphi$ and
$o$ (the token stack holding the tokens of $\varphi$ reversed, the output stack holding $o$, and
everything else empty), the emitter reaches, within at most $L(8L + 12) + 2m + 3$ steps, label
$\mathrm{h0}$ with some internal state and the stacks of the emitter state of $\varphi$ and $o$
after phase A (the tokens of $\varphi$ on $F$, the variable stack of the distinct variables of
$\varphi$ on $V$, $m$ on the counters $C$ and $P$, $3m$ on $M$, $o$ on the output stack, and
everything else empty).
