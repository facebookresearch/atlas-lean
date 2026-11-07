# Correctness and running time of the Hamiltonian path verifier

Let $x$ and $w$ be bit
lists. Start the verifier at its start label, with either value of its Boolean variable, with
$x$ on stack $\mathsf{X}$ and $w$ on stack $\mathsf{W}$ (as bit symbols, first bit on top) and
all other stacks empty. Then within $100(|x| + |w| + 1)^4$ steps it reaches the label
$\mathrm{yes}$ if the Hamiltonian path check accepts $x$ and $w$, and the label $\mathrm{no}$
otherwise.

The machine in fact takes quadratically many steps; the theorem states only the quartic bound.
