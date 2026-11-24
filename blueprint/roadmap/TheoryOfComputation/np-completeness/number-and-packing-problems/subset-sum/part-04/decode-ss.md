# Decoding a SUBSET-SUM instance

A block holding a bit string $p$ writes each bit $b$ of $p$
as the two bits $1, b$ and ends with a single $0$. The decoder reads a bit string $x$ as one block
holding the target $t$, followed by blocks holding numbers $a_1, \dots, a_n$ that run exactly to
the end of $x$, where each block must hold the canonical binary representation of its number
(least significant bit first, no trailing $0$). It returns the list $(a_1, \dots, a_n)$ together
with $t$, and fails if $x$ does not split this way.
