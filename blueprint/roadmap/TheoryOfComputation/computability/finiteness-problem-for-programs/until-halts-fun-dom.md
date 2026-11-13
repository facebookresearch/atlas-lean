# Domain of the until-halts function

For a code $c$ of a partial recursive function, let
$u_c$ be the partial function on $\mathbb{N}$ that on input $j$ is undefined if $c$ halts on input
$0$ within $j$ steps (the step-bounded evaluation of $c$ on input $0$ with bound $j$ returns a
value) and outputs $0$ otherwise. Then for every $k \in \mathbb{N}$, $u_c$ is defined at $k$ if
and only if $c$ does not halt on input $0$ within $k$ steps.
