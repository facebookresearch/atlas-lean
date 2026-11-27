# What the HAMPATH verifier accepts

For bit strings $x$ and $w$, the HAMPATH verifier
accepts $(x, w)$ if and only if there are natural numbers $s$, $t$, $n$, a list $es$ of pairs of
natural numbers and a list $p$ of natural numbers such that $x$ is the PATH encoding of
$(s, t, n, es)$, $w$ is the witness encoding of $p$, and $p$ is a Hamiltonian path from $s$ to $t$
in the digraph on $0, \dots, n - 1$ with edge list $es$.
