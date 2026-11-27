# Doubling pass doubles every number in a list

For every list $(a_1, \dots, a_k)$ of natural numbers, the [doubling pass](transform.md) from
phase start maps the concatenation of the blocks of $a_1, \dots, a_k$ to the concatenation of
the blocks of $2a_1, \dots, 2a_k$. Here the block of a natural number $m$ is its binary digits, least significant first (none for $m = 0$), each digit $c$ written as the two bits true, $c$, followed by a final false.
