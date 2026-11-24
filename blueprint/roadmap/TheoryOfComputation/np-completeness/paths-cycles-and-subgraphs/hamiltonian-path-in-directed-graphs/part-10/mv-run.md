# Moving a stack of bits

Suppose the verifier's instruction at label $p$ is the bit-moving
loop from a stack $a$ to a different stack $b$, continuing at label $p'$ when done. If stack $a$
holds exactly the bits of a list $l$, then from label $p$ in any internal state the verifier
takes exactly $|l| + 1$ steps to reach label $p'$, in some internal state, with stack $a$ empty,
stack $b$ holding the bits of $l$ in reverse order followed by its old contents, and every other
stack unchanged.
