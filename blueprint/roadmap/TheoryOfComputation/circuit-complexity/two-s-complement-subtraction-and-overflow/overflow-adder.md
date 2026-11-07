# The overflow adder

The $n$-bit overflow adder is the $n$-bit ripple-carry adder with one
extra XOR gate. It has the same $2n + 1$ inputs (the bits of the two summands, then the carry in)
and $5n + 1$ gates: the $5n$ gates of the ripple-carry adder, followed by an XOR of the carry into
bit $n - 1$ and the carry into bit $n$ (the carry out). Here the carry into bit $0$ is the carry
in, and for $n = 0$ the index $n - 1$ is read as $0$. Its $n + 2$ outputs are the ripple-carry
adder's $n$ sum bits and carry out, followed by the new gate, the signed-overflow flag.
