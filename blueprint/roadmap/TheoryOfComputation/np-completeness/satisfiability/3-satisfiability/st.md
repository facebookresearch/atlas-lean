# Stack contents of the SAT-to-3SAT emitter

For a list $t$ of tokens, a list $o$ of bits
and $z, c \in \mathbb{N}$, $\mathrm{st}(t, o, z, c)$ is the stack contents of the emitter machine
in which the token stack holds $t$, the output stack holds $o$, the fresh counter holds exactly
$z$ copies of the clause token $\mathrm{cl}$, the output clause count holds exactly $c$ copies of
$\mathrm{cl}$, and the two scratch counters are empty.
