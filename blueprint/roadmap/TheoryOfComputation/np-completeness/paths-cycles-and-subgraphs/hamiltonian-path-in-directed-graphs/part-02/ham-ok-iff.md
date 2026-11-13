# The Hamiltonian path check is correct

For all natural numbers $n$, $s$, $t$, every edge
list $E$ and every list $p$ of natural numbers, the Hamiltonian path check on $(n, E, s, t, p)$
returns true if and only if $p$ is a Hamiltonian path from $s$ to $t$ in the digraph on
$\{0, \dots, n-1\}$ with edge list $E$.
