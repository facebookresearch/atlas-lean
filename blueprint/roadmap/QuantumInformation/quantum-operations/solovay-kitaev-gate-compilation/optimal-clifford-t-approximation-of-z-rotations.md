# Ross-Selinger: optimal Clifford+T approximation of z-rotations

There is a probabilistic algorithm that, given $\theta$ and $\varepsilon > 0$, outputs an ancilla-free single-qubit Clifford+T circuit approximating $R_z(\theta) = \mathrm{diag}(e^{-i\theta/2}, e^{i\theta/2})$ within $\varepsilon$ in operator norm. Its guarantees depend on the factoring regime:

- With an oracle for integer factoring, the output has the smallest $T$-count of any single-qubit Clifford+T circuit approximating $R_z(\theta)$ within $\varepsilon$.
- Without a factoring oracle, under a number-theoretic hypothesis on the primality of the integers produced by the algorithm, the output has expected $T$-count $m + O(\log\log(1/\varepsilon))$, where $m$ is the $T$-count of the second-to-optimal solution. In the typical case $m$ is the information-theoretic count $3\log_2(1/\varepsilon)$, giving $T$-count $3\log_2(1/\varepsilon) + O(\log\log(1/\varepsilon))$; this is a typical-case statement, not a per-instance optimality guarantee.

Under the same hypothesis the expected running time is $O(\mathrm{polylog}(1/\varepsilon))$, with or without the factoring oracle.

## Proof sketch

Look for $U = \begin{pmatrix} u & -t^\dagger \\ t & u^\dagger \end{pmatrix}$ with $u, t \in \mathbb{Z}[\tfrac{1}{\sqrt2}, i]$. Suitable candidates $u$ are the solutions of a two-dimensional grid problem (a point of $\mathbb{Z}[\omega]$ in a thin convex region, together with its $\sqrt2$-conjugate in a second convex region), enumerated in order of increasing denominator exponent by grid operators that normalize the two regions. For each candidate, the norm equation $t^\dagger t = 1 - u^\dagger u$ is solved in $\mathbb{Z}[\omega]$, which requires factoring an integer; without an oracle only easily factored (for example prime) instances are accepted. The accepted unitary has entries in the ring, so exact synthesis converts it into a Clifford+T circuit.

## Proof depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)
- [Volume lower bound: logarithmic word length is necessary](volume-lower-bound-for-gate-approximation.md)
- [Kliuchnikov-Maslov-Mosca: exact synthesis of single-qubit Clifford+T unitaries](exact-synthesis-of-clifford-t-unitaries.md)

## Sources

- Neil J. Ross, Peter Selinger, "Optimal ancilla-free Clifford+T approximation of z-rotations", Quantum Information and Computation 16 (2016); arXiv:1403.2975.
