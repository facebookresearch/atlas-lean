# The 3-COLOR emitter

The emitter whose stacks, alphabets, labels, program and start label
are those of the 3-COLOR emitter machine, which exits at the machine's final label, reads the
tokens of a CNF formula from stack $T$ and writes its output bits on stack $O$ (both symbol maps
being the identity), and has step bound $B(n) = 500 (n + 1)^4$ for $n$ tokens. Its output for a
CNF formula $\varphi$ is the encoded 3-COLOR instance of $\varphi$, and for an undecodable input
the encoding of the complete graph $K_4$.
