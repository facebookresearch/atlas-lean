# No-instances of the 2-local Hamiltonian problem

A bitstring $x$ is a no-instance when
decoding it under the canonical bitstring encoding gives a tuple $(n, (h_1, \dots, h_m), a, b)$ of
a natural number $n$, a list of 2-local terms $h_1, \dots, h_m$ and two encoded rational numbers,
whose values we also write $a$ and $b$, such that every $h_l$ is valid on $n$ qubits,
$b - a \ge 1/(m + 1)$, and the Hamiltonian $H$ of $h_1, \dots, h_m$ on $n$ qubits is Hermitian
and has ground energy at least $b$.
