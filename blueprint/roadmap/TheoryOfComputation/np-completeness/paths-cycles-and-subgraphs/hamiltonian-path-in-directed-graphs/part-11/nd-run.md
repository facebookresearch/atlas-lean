# The repeat scan of the Hamiltonian path verifier

For a list $p$ of natural numbers
write $\mathrm{enc}(p)$ for its witness encoding: each entry in unary (that many copies of
`true`) followed by `false`. Let $a$ be a natural number and $q$, $d$ lists of natural numbers.
Suppose that the verifier's stacks hold, as bit symbols with the first bit on top, the bits of
$\mathrm{enc}(q)$ on $\mathsf{W}$, the bits of $\mathrm{enc}(d)$ in reverse order on
$\mathsf{Z}$, $a$ copies of the bit `true` on $\mathsf{A}$, and nothing on $\mathsf{R}$, the
other stacks being arbitrary. Started at label $\mathrm{nd}$ with either value of its Boolean
variable, the verifier reaches, within $4|\mathrm{enc}(q)| + |\mathrm{enc}(d)| + 2$ steps, the
label $\mathrm{no}$ if $a$ is an entry of $q$ and the label $\mathrm{incC}$ otherwise. In the
second case its stacks are then the initial ones except that $\mathsf{W}$ holds the bits of the
encoding of $d$ followed by $q$, and $\mathsf{Z}$ is empty.
