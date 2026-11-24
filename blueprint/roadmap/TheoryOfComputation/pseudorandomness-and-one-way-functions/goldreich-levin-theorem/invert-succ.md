# Inversion success probability of a circuit

For a list $C$ of serialized gates and a map
$\pi$ from $n$-bit strings to $n$-bit strings, the inversion success probability of $C$ against
$\pi$ is the rational number $N / 2^n$, where $N$ is the number of $n$-bit strings $x$ such that
the outputs of $C$ on input $\pi(x)$, taken as its last $n$ gate values, are exactly $x$.
