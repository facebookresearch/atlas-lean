# Computing an output means halting with it

A deterministic multi-tape Turing machine
computes the output $o$ on input $w$ if and only if there is a step $t$ at which the run from the
initial configuration on $w$ halts (it is halted after $t$ steps and not halted after any $s < t$
steps) and the configuration it reaches after $t$ steps has output tape $o$.
