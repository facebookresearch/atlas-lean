# Gate values of an encoded circuit

Let $C = (g_0, \dots, g_{m-1})$ be a list of gates,
each encoded as a (kind, references) pair, let $\alpha$ be a list of booleans and let $n$ be a
natural number. The gate values of $C$ on $\alpha$ are the values $(v_0, \dots, v_{m-1})$ of the
flat Boolean circuit on $n + 2$ inputs obtained by decoding every $g_j$, when input $i$ is given
entry $i$ of $\alpha$, read as false when $i$ is at least the length of $\alpha$.
