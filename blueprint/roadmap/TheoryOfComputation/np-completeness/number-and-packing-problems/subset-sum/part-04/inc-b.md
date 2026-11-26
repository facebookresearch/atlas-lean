# Adding a carry bit

For a carry bit $c$ and a bit string $u$ (least significant bit
first), $\mathrm{inc}(c, u)$ adds $c$ to $u$ by ripple carry: on the empty string it is $[1]$ if
$c$ is true and empty otherwise, and on a string with first bit $a$ and rest $u'$ it is the bit
$a \oplus c$ followed by $\mathrm{inc}(a \wedge c, u')$.
