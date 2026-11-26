# Nondeterministic decision in bounded space

Let $M$ be a nondeterministic multi-tape
Turing machine over the boolean alphabet, $s : \mathbb{N} \to \mathbb{N}$ and $L$ a set of
bitstrings. Then $M$ decides $L$ in space $s$ if, for every input $x$, every computation path of
$M$ on $x$ visits at most $s(|x|)$ work-tape cells in total, where $|x|$ is the length of $x$,
and for every bitstring $x$, $x \in L$ if and only if some computation path of $M$ on $x$ ends in
a halted configuration whose output is the one-element list $[\mathrm{true}]$.
