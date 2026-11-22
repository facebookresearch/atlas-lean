# The primality decision problem

The primality decision problem is the decision problem
that accepts a bitstring $x$ exactly when the natural number decoded from $x$ is prime, and rejects $x$
otherwise. A bitstring is decoded as the binary digits of a natural number, least significant bit
first; a nonempty bitstring whose last bit is false is read as if a final true bit followed it, so
every bitstring decodes (the empty bitstring to $0$, and the bitstring $0$ to $2$).
