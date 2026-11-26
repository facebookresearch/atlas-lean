# The edge-list check of the Hamiltonian-path verifier

Let $r$ and $acc$ be bit lists, and
let the stacks $St$ hold $r$ on the input stack $X$ and the reverse of $acc$ on the save stack
$E$. Started at the label $\mathsf{vE}$ with any flag value, the verifier reaches within at most
$2|r| + 1$ steps the label $\mathsf{vEb}$ if $r$ decodes as an edge list (a sequence of pairs of
unary numbers, each a block of ones ended by a zero) and the label $\mathsf{no}$ otherwise. When
$r$ decodes, the final stacks are $St$ with $X$ emptied and $E$ holding the reverse of the
concatenation of $acc$ and $r$ (that is, $r$ reversed on top of $acc$ reversed), all other
stacks unchanged.
