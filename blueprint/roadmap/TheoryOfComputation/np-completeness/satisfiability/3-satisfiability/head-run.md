# The 3SAT emitter reads a literal marker

For all booleans $f$ and $p$, every token list
$t$, output bit list $o$, natural numbers $z$ and $c$, and flag $v$, there is a flag $v'$ such
that the 3SAT emitter machine, started at the literal label for $f$ with flag $v$, token stack
the literal marker of polarity $p$ followed by $t$, output stack $o$, fresh counter $z$, clause
count $c$ and empty scratch counters, reaches the renamed-literal label for $(f, p)$ with flag
$v'$ and token stack $t$ as follows. If $f$ is true (the literal is the first walked in its
clause), this takes exactly $1$ step and leaves the output stack and the fresh counter unchanged.
If $f$ is false, it takes exactly $3z + 6$ steps, the output stack becomes the code of the
literal $(\mathrm{fresh}(z), \mathrm{true})$ followed by $o$, where
$\mathrm{fresh}(z) = 2^{z+1} + 1$, and the fresh counter becomes $z + 1$. In both cases the
clause count stays $c$ and the scratch counters stay empty.
