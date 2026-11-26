# Closing an output clause in the SAT-to-3SAT emitter

Let $f$ be a Boolean, $R$ a list of
tokens, $o$ a list of bits and $z, c \in \mathbb{N}$, and let $m = 1$ if $f$ is true and $m = 2$
otherwise. Start the emitter machine at its clause-closing label $\mathrm{aft}(f)$, with any
internal state, with stack contents $\mathrm{st}(R, o, z, c)$: token stack $R$, output stack $o$,
fresh counter $z$, output clause count $c$ and empty scratch counters.

If the top of $R$ is a literal marker, then after exactly $3z + 7$ steps the machine is at the
label $\mathrm{lit}(\mathrm{false})$ with stack contents $\mathrm{st}(R, o', z, c + 1)$, where the
list $o'$ consists of $m + 1$ copies of true, then false, then the code of the literal
$(\mathrm{fresh}(z), \mathrm{false})$, then $o$. Otherwise (in particular when $R$ is empty),
after exactly one step the machine is at the label $\mathrm{start}$ with stack contents
$\mathrm{st}(R, o', z, c + 1)$, where $o'$ consists of $m$ copies of true, then false, then $o$.
In both cases the final internal state is unspecified.
