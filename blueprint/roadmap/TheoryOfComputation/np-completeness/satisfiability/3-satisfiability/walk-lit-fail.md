# A capped walk fails on a literal past the third

Let $n \in \mathbb{N}$ with $n \ge 3$
and let $w_n$ be the walking label after $n$ literals; stacks are lists written top first,
$\mathrm{bit}(b)$ is the name-bit symbol carrying the Boolean $b$ and $\mathrm{lit}(p)$ is the
polarity marker of polarity $p$. Let $l = (i, p)$ be a literal with variable index
$i \in \mathbb{N}$ and polarity $p$, let $e_1, \dots, e_m$ be the binary encoding
$\mathrm{encodeNat}(i)$ of $i$, let $R$ and $U$ be lists of symbols and $v$ a Boolean. Then
there are a Boolean $v'$ and stacks $S'$ such that the capped clause-length filter (cap flag
true) goes in exactly one step from label $w_n$, local variable $v$, token stack
$\mathrm{lit}(p), \mathrm{bit}(e_m), \dots, \mathrm{bit}(e_1)$ on top of $R$ and side stack $U$
to the label $\mathrm{fail}$ with local variable $v'$ and stacks $S'$.
