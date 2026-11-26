# Evaluation of a succinct circuit (Succinct Circuit Value)

Let $C$ be a list of encoded
gates, $n \in \mathbb{N}$ and $x$ a list of booleans. The gate values of the circuit with $2^n$
gates succinctly described by $C$ on input $x$ form the list $(v_0, \dots, v_{2^n - 1})$, where
each $v_i$ is the value of gate $i$ given $x$ and the values $(v_0, \dots, v_{i-1})$ of the
earlier gates.
