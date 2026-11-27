# Worst-case to average-case encodings stay in E

For every language $L\in\mathsf{E}$, the language encoding the truth tables of $L$ by a locally list-decodable code (the Sudan–Trevisan–Vadhan concatenation of a low-degree extension over a field of size $\mathrm{poly}(2^{n})$ with a Hadamard code) is again in $\mathsf{E}$. This membership is the step that keeps the hard function inside $\mathsf{E}$ when local list decoding turns worst-case hardness into average-case hardness.

## Proof sketch

The encoded bit at position $(z,r)$ is $\langle\hat f(z),r\rangle$ for the low-degree extension $\hat f$; computing it sums $2^{O(n)}$ truth-table entries with Lagrange weights over the field, each obtained by running the $\mathsf{E}$ algorithm, all in time $2^{O(n)}$.

## Depends on

- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)

## Sources

- Madhu Sudan, Luca Trevisan and Salil Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and System Sciences 62(2), 236–266, 2001 (Sections 4–5: the low-degree extension over a field of size $2^{O(n)}$ concatenated with the Hadamard code).
