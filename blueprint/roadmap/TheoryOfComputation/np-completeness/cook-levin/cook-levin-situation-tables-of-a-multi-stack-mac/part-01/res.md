# Effect of a situation

Let $E$ be an encoding of a finite multi-stack Turing machine $M$
and $i$ a natural number. Let $(l, v)$, an optional label and a state, be the result of decoding
the label/state code of situation $i$ with the inverse (label, state) numbering of $E$, and let
$W$ be the decoded windows of situation $i$. The effect of situation $i$ is the situation step of
$M$ from $l$, $v$ and $W$: a new optional label, a new state, the symbols left pushed on each
stack, and the number of original symbols consumed from each stack.
