# Gates of a flat Boolean circuit

A gate of a flat Boolean circuit on $n$ inputs is one of:
an input variable $x_i$ for some $i < n$; a Boolean constant; a negation gate with one predecessor
index $a \in \mathbb{N}$; a conjunction gate or a disjunction gate with a list of predecessor
indices; or a mod gate with a modulus $m \in \mathbb{N}$ and a list of predecessor indices.

Predecessors are referred to by their positions in the circuit; that gate $j$ refers only to
gates before $j$ is a separate well-formedness condition on circuits.
