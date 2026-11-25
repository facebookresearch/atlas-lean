# Encoded reduction from SUBSET-SUM to PARTITION

The map on bitstrings that sends $x$ to the canonical encoding of the
[padded instance](from-subset-sum.md) $(a_1 + \dots + a_n, 2t, a_1, \dots, a_n)$ when $x$ decodes
as a SUBSET-SUM instance with numbers $a_1, \dots, a_n$ and target $t$, and to the canonical
encoding of the one-entry list $(1)$, a no-instance of PARTITION, otherwise. A bitstring decodes
as a SUBSET-SUM instance when it is the block of $t$ followed by the blocks of
$a_1, \dots, a_n$, each holding the canonical binary code of its number; here the block of a natural number $m$ is its binary digits, least significant first (none for $m = 0$), each digit $c$ written as the two bits true, $c$, followed by a final false.
