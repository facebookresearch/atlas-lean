# CSS codes correct $\lfloor (d - 1) / 2 \rfloor$ errors

Let $C_2 \subseteq C_1 \subseteq \mathbb{F}_2^n$ be binary linear codes such that every nonzero word of
$C_1$ and every nonzero word of $C_2^{\perp}$ has Hamming weight at least $d$. Let $P$ be the
orthogonal projector onto the CSS code $Q_{C_1, C_2}$, the span of the
[codewords](codeword.md) $|c_w\rangle$ with $w \in C_2^{\perp}$. Then the Pauli errors
$X^a Z^b$ acting on at most $t = \lfloor (d - 1)/2 \rfloor$ qubits, that is with
$2\,|\operatorname{supp} a \cup \operatorname{supp} b| + 1 \le d$, are
[correctable](../knill-laflamme-conditions/is-correctable.md) on the code, all by one recovery
channel.

Calderbank and Shor state that "if $C_1$ and $C_2^{\perp}$ have minimum distance $d$, then the
quantum code $Q_{C_1, C_2}$ can correct $t = \lfloor (d-1)/2 \rfloor$ errors", for an arbitrary
decoherence of any $t$ qubits. The Kraus operators of such a decoherence are linear combinations
of Pauli operators on those qubits, and correctable families are closed under linear combinations
(Knill and Laflamme, Theorem 3.1), so the Pauli form is equivalent.

For $C_1$ the $[7,4,3]$ Hamming code and $C_2 = C_1^{\perp}$, $C_2^{\perp} = C_1$ has minimum
distance $3$, and the theorem gives a seven-qubit code correcting one error.

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section III (the statement before equation (5)) and Section IV.
- E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55 (1997), 900–911, arXiv:quant-ph/9604034, Theorem 3.1.
