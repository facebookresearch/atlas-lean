# Worst-case to average-case encodings stay in E

For every language $L\in\mathsf{E}$, the language encoding the truth tables of $L$ by a locally list-decodable code (the Sudan–Trevisan–Vadhan concatenation of a low-degree extension over a field of size $\mathrm{poly}(2^{n})$ with a Hadamard code) is again in $\mathsf{E}$. Consequently, if $\mathsf{E}$ requires circuits of size $2^{\Omega(n)}$ in the worst case, it contains a function that is average-case hard against circuits of size $2^{\Omega(n)}$ (agreement at most $1/2+2^{-\Omega(n)}$), which suffices for derandomization.

## Proof sketch

The encoded bit at position $(z,r)$ is $\langle\hat f(z),r\rangle$ for the low-degree extension $\hat f$; computing it sums $2^{O(n)}$ truth-table entries with Lagrange weights over the field, each obtained by running the $\mathsf{E}$ algorithm, all in time $2^{O(n)}$. Local list decoding converts any good average-case circuit for the encoding into a worst-case circuit for $L$.

## Depends on

- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)

## Proof depends on

- [Average-case hardness in E derandomizes BPP](../../derandomization/average-case-hardness-in-e-derandomizes-bpp.md)

## Sources

- Madhu Sudan, Luca Trevisan and Salil Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and System Sciences 62(2), 236–266, 2001 (Sections 4–5: the low-degree extension over a field of size $2^{O(n)}$ concatenated with the Hadamard code, and its local list decoding).
