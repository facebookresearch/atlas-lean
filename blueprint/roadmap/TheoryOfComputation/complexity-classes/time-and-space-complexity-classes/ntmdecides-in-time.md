# Nondeterministic decision in bounded time

Let $M$ be a nondeterministic multi-tape
Turing machine over the boolean alphabet, $t : \mathbb{N} \to \mathbb{N}$ and $L$ a set of
bitstrings. Then $M$ decides $L$ in time $t$ if, for every input $x$, every computation path of
$M$ on $x$ with at least $t(|x|)$ steps ends in a halted configuration, where $|x|$ is the length
of $x$, and for every bitstring $x$, $x \in L$ if and only if some computation path of $M$ on $x$
ends in a halted configuration whose output is the one-element list $[\mathrm{true}]$.
