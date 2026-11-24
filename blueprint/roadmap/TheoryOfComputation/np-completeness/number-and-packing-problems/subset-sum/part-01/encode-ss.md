# Bit-string encoding of SUBSET-SUM instances

The instance with numbers $a_1, \dots, a_r$
and target $t$ is encoded as the block of $t$ followed by the blocks of $a_1, \dots, a_r$ in
order. The block of a number is its binary expansion, least significant bit first and empty for
the number $0$, made self-delimiting by writing each bit $c$ as $1c$ and appending a final $0$.
