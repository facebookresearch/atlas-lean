# Fresh-literal subroutine of the 3SAT emitter

For all booleans $s$ and $x$, every token
list $t$, output bit list $o$, natural numbers $z$ and $c$, and flag $v$, there is a flag $v'$
such that the 3SAT emitter machine, started at the fresh-literal label for $(s, x)$ with flag
$v$, token stack $t$, output stack $o$, fresh counter $z$, clause count $c$ and empty scratch
counters, reaches in exactly $3z + 5$ steps the return label for $(s, x)$ with flag $v'$, token
stack $t$, output stack the code of the literal $(\mathrm{fresh}(z), s)$ followed by $o$, where
$\mathrm{fresh}(z) = 2^{z+1} + 1$, fresh counter $z + 1$ if $s$ is true and $z$ if $s$ is false,
clause count $c$ and empty scratch counters. The return label is the renamed-literal label for a
literal of polarity $x$ that is not the first walked in its clause if $s$ is true, and the
clause-closing label for first-flag $x$ if $s$ is false.

The subroutine prepends $\mathrm{true}, \mathrm{true}, \mathrm{false}, s$, copies the fresh
counter $U$ into the scratch counter $Z$ (restoring $U$ through the scratch counter $W$),
prepends $\mathrm{true}, \mathrm{false}$ per unit of $Z$, then prepends
$\mathrm{true}, \mathrm{true}$, and for $s$ true adds one to $U$.
