# Every syndrome is the syndrome of a Pauli operator

Let $S$ be a stabilizer group on $n$ qubits with independent generators $M_1, \dots, M_r$. For every
$s \in \mathbb{F}_2^r$ there is a Pauli operator $E = X^a Z^b$ whose [error syndrome](error-syndrome.md) is $f(E) = s$.

Proof: writing $v_j \in \mathbb{F}_2^{2n}$ for the vector of $M_j$, the conditions $\omega(v_j, (a, b)) = s_j$ are $r$
linear equations in $2n$ unknowns. The map $e \mapsto (\omega(v_j, e))_j$ is onto $\mathbb{F}_2^r$, because the $v_j$ are
linearly independent and $\omega$ is nondegenerate.

Gottesman uses this to count dimensions: each of the $2^r$ syndromes is realised by some $E$, which maps the code space
unitarily onto the joint eigenspace of $M_1, \dots, M_r$ with eigenvalues $(-1)^{s_j}$; these eigenspaces are pairwise
orthogonal and fill the $2^n$-dimensional space, so the code has dimension $2^{n-r}$.

## Depends on

- [Error syndrome of a stabilizer code](error-syndrome.md)

## Proof depends on

- [Symplectic product of Pauli operators](symplectic-product-of-pauli-operators.md)

## Background

- [Dimension of a stabilizer code](../finrank-stabilizer-code.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 3.1, Lemma 1, and Section 2.3, the proof of Theorem 5.
