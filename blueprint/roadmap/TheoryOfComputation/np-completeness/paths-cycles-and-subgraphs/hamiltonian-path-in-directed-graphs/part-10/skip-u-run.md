# The unary mover of the Hamiltonian path verifier moves a terminated number

Let
$\mathsf{src} \ne \mathsf{dst}$ be stacks and $\ell$, $m$ labels such that the verifier's
statement at $\ell$ is the unary mover from $\mathsf{src}$ to $\mathsf{dst}$ with own label
$\ell$ and next label $m$. Let $k$ be a natural number and $r$ a bit list, and suppose that
$\mathsf{src}$ holds $k$ copies of `true`, then `false`, then $r$ (as bit symbols, first bit on
top). Then from label $\ell$, with either value of the Boolean variable, the verifier reaches
label $m$ in exactly $k + 1$ steps, with $\mathsf{src}$ holding the bits of $r$, with
$\mathsf{dst}$ holding the bit `false` followed by $k$ copies of the bit `true` on top of its
previous contents, and with every other stack unchanged.
