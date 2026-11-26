# Running the swapping machine

For bit lists $a$ and $b$, the swapping machine runs from its initial configuration, holding the tagged pair encoding of $(a, b)$ on its main stack, to its halting configuration, holding the tagged pair encoding of $(b, a)$ there with both scratch stacks empty and the internal state reset, in exactly $2|a| + 2|b| + 7$ steps.
