# Depth of an appended gate

After a gate is appended to a straight-line circuit $c$, the new last output has the depth of the gate
over the wire depths of $c$: one more than the largest depth among the wires it reads, where input wires
have depth $0$ and gates of $c$ have their depth in $c$. A gate that reads no wires has depth $1$.
