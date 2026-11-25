# Outputs of an encoded circuit (Succinct Circuit Value)

Let $C$ be a list of encoded
gates, $a$ a list of booleans and $k, n \in \mathbb{N}$. Decode each gate of $C$ into a gate of a
flat Boolean circuit on $n$ inputs and evaluate the decoded circuit with input $j < n$ set to the
entry $a_j$ of $a$, read as false when $j$ is at least the length of $a$. The outputs of $C$ on
$a$ are the last $k$ of the resulting gate values, or all of them if $C$ has fewer than $k$
gates.
