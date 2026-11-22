# Well-formed description circuits (Succinct Circuit Value)

A list $C$ of encoded gates
is a well-formed description circuit on $n$ inputs when $C$ has at least $2n + 3$ gates and the
flat Boolean circuit on $n$ inputs obtained by decoding each gate of $C$ is well-formed, that
is, every gate references only strictly earlier gates.

The length bound guarantees that the $2n + 3$ outputs read as a gate description exist; without
it, missing outputs would silently read as false.
