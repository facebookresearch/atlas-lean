# The SUBSET-SUM verifier machine

Let $x$ and $w$ be lists of bits and $v$ a Boolean, and
let $S$ assign stack contents with the bits of $x$ on $X$, the bits of $w$ on $W$ and every other
stack empty. Started at the start label with internal state $v$ and stacks $S$, the verifier
program reaches, within $16(|x| + |w| + 1)^3$ steps, a configuration with label $\mathsf{yes}$
if the SUBSET-SUM check accepts $(x, w)$, and with label $\mathsf{no}$ otherwise.
