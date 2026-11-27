# The HAMPATH verifier

Given bit strings $x$ and $w$, the verifier decodes $x$ as a PATH
instance, consisting of a start vertex $s$, a target vertex $t$, a vertex count $n$ and an edge
list $E$, and decodes $w$ as a witness, a list $p$ of natural numbers each written in unary. If
both decodings succeed, it accepts exactly when the Hamiltonian path check passes, that is, when
$p$ is a Hamiltonian path from $s$ to $t$ in the digraph on $\{0, \dots, n-1\}$ with edge list
$E$. If either decoding fails, it rejects.
