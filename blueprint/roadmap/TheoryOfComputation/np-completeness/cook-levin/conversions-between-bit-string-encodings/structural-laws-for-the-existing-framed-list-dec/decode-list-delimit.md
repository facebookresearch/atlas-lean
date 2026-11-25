# List decoder consumes one raw payload at a time

Let $\alpha$ be a type with a canonical bit-string encoding and use the canonical list decoder of
[decoded list length](../size-bounds-for-the-canonical-framed-codecs/decoded-list-length-le.md). For all bit
strings $p$ and $r$, the list decoder on the framed form of $p$ followed by $r$ succeeds exactly when the decoder of
$\alpha$ returns some $a$ on $p$ and the list decoder returns some list $(a_1, \ldots, a_k)$ on $r$, and then it
returns $(a, a_1, \ldots, a_k)$.
