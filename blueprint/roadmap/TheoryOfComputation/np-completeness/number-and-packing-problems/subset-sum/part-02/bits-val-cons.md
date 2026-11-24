# Value of a bit list with a leading bit

Write $\mathrm{val}(l)$ for the value of a bit list
$l$ read as a binary number least significant bit first, and for a bit $b$ write $[b]$ for $1$ if
$b$ is true and $0$ if $b$ is false. For every bit $b$ and every bit list $l$, the list with first
entry $b$ followed by $l$ has value $[b] + 2 \cdot \mathrm{val}(l)$.
