# Name copy loop of the 3SAT emitter

Let $f$ and $e$ be booleans, $R$ a token list whose
first token, if there is one, is not a name bit, $z$ and $c$ natural numbers, $b_1, \dots, b_m$
bits, $v$ a flag and $o$ an output bit list. Then there is a flag $v'$ such that the 3SAT emitter
machine, started at the copy label for $(f, e)$ with flag $v$, token stack the name-bit tokens
$b_1, \dots, b_m$ followed by $R$, output stack $o$, fresh counter $z$, clause count $c$ and
empty scratch counters, reaches in exactly $m + 1$ steps the after-literal label for $f$ with
flag $v'$, token stack $R$, output stack
$P, \mathrm{true}, b_m, \mathrm{true}, b_{m-1}, \dots, \mathrm{true}, b_1$ followed by $o$, and
the same counters, where $P$ is the pair $\mathrm{true}, \mathrm{false}$ if $e$ is true or
$m > 0$, and is empty otherwise.

Each name bit $b$ read prepends $b$ and then $\mathrm{true}$; the leading pair
$\mathrm{true}, \mathrm{false}$ codes the low bit $0$ of a renamed name $2n$.
