# Domain of the halts-within function

For a code $c$ of a partial recursive function, let
$h_c$ be the partial function on $\mathbb{N}$ that on input $j$ outputs $0$ if $c$ halts on input
$0$ within $j$ steps (the step-bounded evaluation of $c$ on input $0$ with bound $j$ returns a
value) and is undefined otherwise. Then for every $k \in \mathbb{N}$, $h_c$ is defined at $k$ if
and only if $c$ halts on input $0$ within $k$ steps.
