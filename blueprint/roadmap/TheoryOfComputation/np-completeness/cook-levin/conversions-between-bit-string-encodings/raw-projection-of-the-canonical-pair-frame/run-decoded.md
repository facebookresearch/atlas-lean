# Raw field projection agrees with the pair decoder

Let $\alpha$ and $\beta$ be types with canonical bit-string encodings, with the pair decoder of [decoded pair
parts](../size-bounds-for-the-canonical-framed-codecs/decoded-pair-parts.md). Let $x$ be a bit string on which the
pair decoder returns $(a, b)$, and let $v$ be a Boolean. Then there are bit strings $p$, $r$ and an internal state
$v'$ such that the [pair-frame splitter](prog.md) goes from label read, internal state $v$, input $x$ and empty left
and scratch stacks to label good, internal state $v'$, input $r$, left stack $p$ and empty scratch stack in at most
$|x| + 1$ steps, the decoder of $\alpha$ returns $a$ on $p$ and the decoder of $\beta$ returns $b$ on $r$.

The machine does not decode either field.
