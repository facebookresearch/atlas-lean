# CSS codeword

For a binary linear code $C_1 \subseteq \mathbb{F}_2^n$ and $w \in \mathbb{F}_2^n$, the CSS codeword
is the vector of amplitudes on the $2^n$ basis states $|v\rangle$ of $n$ qubits given by

$$|c_w\rangle = \sum_{v \in C_1} (-1)^{v \cdot w}\, |v\rangle,$$

that is, the function $v \mapsto (-1)^{v \cdot w}$ on $C_1$ and $0$ off $C_1$. Calderbank and
Shor's equation (2) includes the factor $2^{-\dim C_1/2}$, which makes it a unit vector (see
[the norm](inner-codeword-self.md)) and is omitted here. They let $v$ range over $C_1$ through
a generator matrix $M$, writing $vM$; summing over $C_1$ directly is the same.

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section III, equation (2).
