# Malformed first frame makes list decoding fail

Let $\alpha$ be a type with a canonical bit-string encoding and use the canonical list decoder of
[decoded list length](../size-bounds-for-the-canonical-framed-codecs/decoded-list-length-le.md). Let $x$ be a
nonempty bit string no prefix of which is the framed form $1 p_1 \cdots 1 p_m 0$ of a bit string $p$. Then the list
decoder fails on $x$.

The empty string is excluded: it decodes to the empty list.
