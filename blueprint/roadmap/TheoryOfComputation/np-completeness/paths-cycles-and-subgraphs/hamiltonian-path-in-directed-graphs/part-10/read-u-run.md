# The unary reader of the Hamiltonian path verifier reads a terminated number

Let
$\mathsf{src} \ne c$ be stacks and $\ell$, $m$ labels such that the verifier's statement at
$\ell$ is the unary reader from $\mathsf{src}$ onto $c$ with own label $\ell$ and next label
$m$. Let $k, j$ be natural numbers and $r$ a bit list, and suppose that $\mathsf{src}$ holds
$k$ copies of `true`, then `false`, then $r$ (as bit symbols, first bit on top) and that $c$
holds $j$ copies of the bit `true`. Then from label $\ell$, with either value of the Boolean
variable, the verifier reaches label $m$ in exactly $k + 1$ steps, with $\mathsf{src}$ holding
the bits of $r$, $c$ holding $k + j$ copies of the bit `true`, and every other stack
unchanged.
