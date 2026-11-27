# Polynomial-time conversion to the verifier's pair encoding

A polynomial-time computation
of the identity map on pairs $(x, w)$ of bit lists, from the canonical bitstring encoding of
$(x, w)$ to the verifier's pair encoding of $(x, w)$ (the bits of $x$, the separator, then the
bits of $w$), by the converter machine, with the bits and the verifier's symbols themselves as
input and output alphabets and time bound $n + 5$: started on the canonical encoding of $(x, w)$,
a list of length $n$, the converter halts within $n + 5$ steps with no bit in its state, the
verifier's pair encoding of $(x, w)$ on its output stack and every other stack empty.
