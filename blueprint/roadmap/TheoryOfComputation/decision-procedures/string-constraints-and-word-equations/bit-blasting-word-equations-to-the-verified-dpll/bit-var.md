# SAT variable index for a bit of a string variable

For natural numbers $i$ (a string variable) and $p$ (a position), the SAT variable of bit $p$ of variable
$i$ is $\langle i, p\rangle + 1$, where $\langle i, p\rangle$ denotes the pairing bijection $\mathbb{N}^2 \to \mathbb{N}$ given by $\langle i, p\rangle = p^2 + i$ if $i < p$ and $\langle i, p\rangle = i^2 + i + p$ otherwise. These indices are positive, so the SAT variable $0$ is
left free (it is used for the constant bit).
