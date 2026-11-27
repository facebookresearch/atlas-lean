# Nondeterministic decision

A nondeterministic multi-tape Turing machine $M$ over the
boolean alphabet decides a set $L$ of bitstrings if, for every bitstring $x$, $x \in L$ if and
only if some computation path of $M$ on $x$ ends in a halted configuration whose output is the
one-element list $[\mathrm{true}]$.
