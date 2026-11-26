# Doubling pass maps a number block to the block of its double

For every natural number $n$ and every bitstring $r$, the [doubling pass](transform.md) from
phase start maps the block of $n$ followed by $r$ to the block of $2n$ followed by the doubling
pass of $r$ from phase start. Here the block of a natural number $m$ is its binary digits, least significant first (none for $m = 0$), each digit $c$ written as the two bits true, $c$, followed by a final false.
