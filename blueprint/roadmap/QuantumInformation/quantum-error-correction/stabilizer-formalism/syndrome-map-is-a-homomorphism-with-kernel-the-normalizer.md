# The syndrome map is a homomorphism with kernel the normalizer

Let $S$ be a stabilizer group with independent generators $M_1, \dots, M_r$ and let $f$ be the
[error syndrome](error-syndrome.md). For all $E, F \in \mathcal{P}_n$:

1. $f(EF) = f(E) + f(F)$;
2. $f(E) = 0$ if and only if $E \in N(S)$, the [normalizer](normalizer-of-a-stabilizer-group-equals-its-centralizer.md) of $S$;
3. $f(E) = f(F)$ if and only if $E$ and $F$ lie in the same coset of $N(S)$ in $\mathcal{P}_n$.

In particular, for errors $E_a, E_b$ with $E_a^{*} E_b \notin N(S)$ the syndromes differ, so measuring the generators
distinguishes them; this is the case "some element of $S$ anticommutes with $E_a^* E_b$" of the
[correctability criterion](../stabilizer-codes-correctability-criterion-and-distance.md).

Proof: (1) is linearity of $\omega$ in the first argument; (2) holds because an element commuting with every generator
commutes with all of $S$; (3) follows from (1) and (2), as $E^2$ is a scalar.

## Depends on

- [Error syndrome of a stabilizer code](error-syndrome.md)
- [The normalizer of a stabilizer group is its centralizer](normalizer-of-a-stabilizer-group-equals-its-centralizer.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](pauli-operators-commute-iff-symplectic-product-vanishes.md)

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.2, the paragraph after equation (3.9).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 3.4 ("two Pauli operators $E$ and $F$ have the same error syndrome iff $E$ and $F$ are in the same coset of $N(S)$ in $P_n$").
