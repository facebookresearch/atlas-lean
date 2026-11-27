# Gate values of an encoded circuit (Succinct Circuit Value)

Let $C$ be a list of encoded
gates, $a$ a list of booleans and $n \in \mathbb{N}$. Decode each gate of $C$ into a gate of a
flat Boolean circuit on $n$ inputs, and assign to input $j < n$ the entry $a_j$ of $a$, read as
false when $j$ is at least the length of $a$. The result is the list of the values of all gates
of the decoded circuit under this assignment, in order.
