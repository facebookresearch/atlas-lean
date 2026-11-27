# Characterization of clocked results

For a code $c$, a list of bits $x$, a clock
$T \in \mathbb{N}$ and a list $l$ of natural numbers, the clocked evaluator returns $l$ on $c$,
$x$ and $T$ if and only if the configuration of $c$ after $T$ clocked steps on $x$ has no
successor step and its output is $l$.
