# Token sequence of a CNF formula

For a CNF formula $\varphi$ with clauses
$C_1, \dots, C_k$ (in order), the token sequence of $\varphi$ is the concatenation of the token
sequences of $C_1, \dots, C_k$. The token sequence of a clause is the concatenation of the token
sequences of its literals, in order, followed by a clause-end symbol; the token sequence of a
literal with variable index $n \in \mathbb{N}$ and polarity $p$ is the bits of the binary
encoding of $n$ (Mathlib's `encodeNat`), each as a name-bit symbol, followed by a polarity
marker for $p$.

The verifier's token stack holds this sequence in reverse order.
