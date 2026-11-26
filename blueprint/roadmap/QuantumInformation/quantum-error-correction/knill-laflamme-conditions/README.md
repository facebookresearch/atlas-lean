# Knill–Laflamme conditions

A quantum code is a subspace $C$ of a finite-dimensional Hilbert space; here it is given by the orthogonal projector $P$ onto it. A family of errors $A_a$ is correctable on $C$ when one recovery channel undoes every error on every code state. Knill and Laflamme's Theorem 3.2 characterises correctability without mentioning the recovery: the errors are correctable if and only if $P A_a^{*} A_b P = c_{ab} P$ for all $a, b$. In an orthonormal basis $|i_L\rangle$ of the code this reads $\langle i_L | A_a^{*} A_b | i_L \rangle = \langle j_L | A_a^{*} A_b | j_L \rangle$ and $\langle i_L | A_a^{*} A_b | j_L \rangle = 0$ for $i \ne j$ (Preskill's equation (7.19)). Necessity follows by inserting the completeness relation of the recovery, sufficiency by constructing the recovery channel explicitly.

- [Correctable errors on a quantum code](is-correctable.md)
- [Correctable errors form a linear space](is-correctable-of-forall-mem-span.md)
- [Necessity of the Knill–Laflamme conditions](knill-laflamme-of-is-correctable.md)
- [Sufficiency of the Knill–Laflamme conditions](is-correctable-of-knill-laflamme.md)
- [The Knill–Laflamme conditions](is-correctable-iff-knill-laflamme.md)
- [Conditions for approximate quantum error correction](conditions-for-approximate-quantum-error-correction.md)

## Related topics

- [CSS codes](../css-codes/README.md): a family of codes whose error-correction theorem is stated with this notion of correctability.
