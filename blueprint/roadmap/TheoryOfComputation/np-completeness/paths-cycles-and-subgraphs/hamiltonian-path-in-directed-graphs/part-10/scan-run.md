# The edge scan of the Hamiltonian path verifier

For a list $e$ of pairs of natural
numbers write $\mathrm{bits}(e)$ for its edge-list encoding, in which each pair $(u, u')$
contributes $u$ copies of `true`, then `false`, then $u'$ copies of `true`, then `false`. Let
$a, b$ be natural numbers and $r$, $d$ lists of pairs of natural numbers. Suppose that the
verifier's stacks hold, as bit symbols with the first bit on top, $\mathrm{bits}(r)$ on
$\mathsf{X}$, $\mathrm{bits}(d)$ in reverse order on $\mathsf{E}$, $a$ copies of the bit `true`
on $\mathsf{A}$, $b$ copies of the bit `true` on $\mathsf{B}$, and nothing on $\mathsf{R}$, the
other stacks being arbitrary. Started at label $\mathrm{scan}$ with either value of its Boolean
variable, the verifier reaches, within $4|\mathrm{bits}(r)| + |\mathrm{bits}(d)| + 2$ steps, the
label $\mathrm{nd}$ if $(b, a)$ is one of the pairs of $r$ and the label $\mathrm{no}$
otherwise. In the first case its stacks are then the initial ones except that $\mathsf{X}$
holds the encoding $\mathrm{bits}$ of the list $d$ followed by $r$, and $\mathsf{E}$ is empty.
