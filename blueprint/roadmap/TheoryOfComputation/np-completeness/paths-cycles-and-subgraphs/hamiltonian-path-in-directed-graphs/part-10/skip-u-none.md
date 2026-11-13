# The unary mover of the Hamiltonian path verifier rejects an unterminated number

Let
$\mathsf{src} \ne \mathsf{dst}$ be stacks and $\ell$, $m$ labels such that the verifier's
statement at $\ell$ is the unary mover from $\mathsf{src}$ to $\mathsf{dst}$ with own label
$\ell$ and next label $m$. Let $l$ be a bit list from which no unary length can be read (that
is, $l$ contains no `false`), and suppose that $\mathsf{src}$ holds the bits of $l$ (as bit
symbols, first bit on top). Then from label $\ell$, with either value of the Boolean variable
and any contents of the other stacks, the verifier reaches label $\mathrm{no}$ within
$|l| + 1$ steps.
