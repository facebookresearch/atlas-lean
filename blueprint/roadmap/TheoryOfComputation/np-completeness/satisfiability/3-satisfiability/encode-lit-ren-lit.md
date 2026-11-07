# Code of a renamed literal

For every literal $(n, p)$, the binary code of the renamed
literal $(2n, p)$ is: the pair $\mathrm{true}, \mathrm{false}$ if $n \neq 0$ and nothing if
$n = 0$, then the pair $\mathrm{true}, b$ for each bit $b$ of the binary representation of $n$
(least significant bit first, no bits for $n = 0$), then $\mathrm{false}, p$.
