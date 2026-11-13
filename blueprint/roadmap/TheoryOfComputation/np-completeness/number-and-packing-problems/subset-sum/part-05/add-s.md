# Adding one payload bit to the sum

The machine statement for adding the payload bit $b$
with carry $c$: pop the top symbol of the sum stack $A$ and read it as a bit $a$ (false if $A$ is
empty or the symbol is not a bit), push the bit $a \oplus b \oplus c$ onto $B$, and go to the label
that adds a chosen number with carry the carry out of $a$, $b$ and $c$ and flag $\lnot b$ (the flag
records whether the bits of the block read so far end in false).
