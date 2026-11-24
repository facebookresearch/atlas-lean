# Ripple-carry addition of bit lists

For a carry-in bit $c$ and bit lists $u$ and $p$, both
least significant bit first, the ripple-carry sum walks $p$. If $p$ is empty, the result is $u$ with
the carry $c$ added (a final carry becomes a new last bit). Otherwise, with $a$ the first bit of $u$
($a$ is false when $u$ is empty) and $b$ the first bit of $p$, the result is the bit
$a \oplus b \oplus c$ followed by the ripple-carry sum of the rest of $u$ and the rest of $p$ with
carry-in the carry out of $a$, $b$ and $c$.
