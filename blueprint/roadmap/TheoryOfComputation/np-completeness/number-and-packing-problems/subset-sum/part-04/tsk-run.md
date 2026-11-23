# Run of the target-output phase of the subset-sum emitter

Let $l$ be a list of bits, let
$l'$ be $l$ with its leading $\mathrm{false}$ bits removed, and let $o$ be a list of bits. Start
the VERTEX-COVER to SUBSET-SUM machine at label $\mathsf{tsk}$ with any state bit and with stacks
$S$ in which stack $\mathsf{T}$ holds exactly the bit symbols of $l$, first bit on top, and the
output stack $\mathsf{O}$ holds $\mathrm{false}$ followed by $o$. Then after exactly $|l| + 1$
steps the machine is at label $\mathsf{done}$ with some state bit and stacks $S'$ in which
$\mathsf{O}$ holds the self-delimiting encoding of the reverse of $l'$ followed by $o$, and every
stack other than $\mathsf{T}$ and $\mathsf{O}$ is as in $S$. Here the self-delimiting encoding of
a list replaces each bit $b$ by $\mathrm{true}, b$ and appends $\mathrm{false}$.
