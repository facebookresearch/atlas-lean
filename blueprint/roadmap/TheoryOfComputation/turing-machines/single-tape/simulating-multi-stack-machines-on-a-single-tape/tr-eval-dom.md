# The emulation halts iff the multi-stack machine halts

Let $M$ be a multi-stack Turing
machine with stacks indexed by $K$, let $k \in K$, and let $L$ be a list over the alphabet of stack
$k$. The single-tape emulation of $M$, started on the tape encoding of the stacks with $L$ on stack
$k$ and all other stacks empty, halts if and only if $M$, started with $L$ on stack $k$ and all
other stacks empty, halts.
