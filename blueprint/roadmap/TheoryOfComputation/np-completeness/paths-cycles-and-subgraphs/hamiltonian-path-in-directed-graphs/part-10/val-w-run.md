# The witness check of the Hamiltonian-path verifier

Let $w$ and $acc$ be bit lists, and
let the stacks $St$ hold $w$ on the witness stack $W$ and the reverse of $acc$ on the save stack
$Z$. Started at the label $\mathsf{vW}$ with any flag value, the verifier reaches within at most
$2|w| + 1$ steps the label $\mathsf{vWb}$ if $w$ decodes as a vertex list (a sequence of unary
numbers, each a block of ones ended by a zero) and the label $\mathsf{no}$ otherwise. When $w$
decodes, the final stacks are $St$ with $W$ emptied and $Z$ holding the reverse of the
concatenation of $acc$ and $w$ (that is, $w$ reversed on top of $acc$ reversed), all other
stacks unchanged.
