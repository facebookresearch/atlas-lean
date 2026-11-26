# The readout run

Let $l$ be a bit list, and start the readout machine at the label
$r_0$ with its internal Boolean variable set to $\mathrm{false}$, $l$ on the input stack $X$ and
the output stack $O$ empty. Then the machine reaches the label $\mathrm{done}$ within $6$ steps,
and $O$ then holds exactly one bit, which is $\mathrm{true}$ if and only if
$l \ne [\mathrm{true}, \mathrm{true}, \mathrm{true}, \mathrm{false}]$, the list that encodes, at
the output of the clocked universal machine, a halt whose output is the single symbol of the bit
$\mathrm{true}$.
