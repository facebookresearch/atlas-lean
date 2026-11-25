# Budgeted runs transport along equal counter values

Let $M$ be a counter machine, let
$K, X \in \mathbb{N}$, let $F$ and $F'$ be counter values with $F = F'$, let $l$ be a label or
the halting state, $v$ a flag, $o$ a list of Booleans and $d$ a configuration. If there is $n$
with $K + n \le X$ such that $M$ goes in exactly $n$ steps from the configuration with label $l$,
flag $v$ and stacks $\mathrm{st}(F', o)$ to $d$, then the same holds from the configuration with
label $l$, flag $v$ and stacks $\mathrm{st}(F, o)$.
