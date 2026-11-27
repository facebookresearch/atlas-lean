# Vitányi: quantum Kolmogorov complexity is at most 2n and most n-qubit states are incompressible

Every $n$-qubit pure state has quantum Kolmogorov complexity $K(|x\rangle\mid n)\le 2n$ up to an additive constant, and a uniformly random $n$-qubit state has $K(|x\rangle\mid n)\ge n-c$ with probability at least $1-2^{-c}$.

Let $K$ be quantum Kolmogorov complexity based on classical descriptions.

1. **Upper bound.** For all $n$-qubit pure states $|x\rangle$, $K(|x\rangle\mid n)\le 2n+O(1)$.
2. **Incompressibility.** For every $c$, under the uniform probability on $n$-qubit pure states, $\Pr\{|x\rangle : K(|x\rangle\mid n)\ge n-c\}\ge 1-2^{-c}$. More precisely, every orthonormal basis $|e_0\rangle,\dots,|e_{2^{n}-1}\rangle$ of the $2^{n}$-dimensional Hilbert space has at least $2^{n}(1-2^{-c})$ vectors with $K(|e_i\rangle\mid n)\ge n-c$.

So, unlike the classical bound $n+O(\log n)$, the trivial description costs up to $2n$ bits, while typical states still need about $n$.

## Expansion

For the upper bound, write $N=2^{n}$; since $\sum_i|\langle e_i|x\rangle|^{2}=1$, some computational basis vector has $|\langle e_i|x\rangle|^{2}\ge 1/N$, and a program of about $n$ bits printing $|e_i\rangle$ plus an approximation part of at most $n$ bits gives $2n$. For incompressibility, a description of length below $n-c$ consists of a program of length $l$ and an approximation part $k$ with $l+k<n-c$; each program's output $|z\rangle$ has squared overlap at least $2^{-k}$ with at most $2^{k}$ vectors of any orthonormal basis, so in total fewer than $2^{n-c}$ basis vectors are compressible. Averaging over random bases gives the probability bound.

## Depends on

- [Quantum Kolmogorov complexity based on classical descriptions](quantum-kolmogorov-complexity.md)

## Proof depends on

- [Few strings have small complexity](../../../kolmogorov-complexity/incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)

## Sources

- Paul M. B. Vitányi, "Quantum Kolmogorov Complexity Based on Classical Descriptions", *IEEE Transactions on Information Theory*, 2001, https://doi.org/10.1109/18.945258; numbering from arXiv:quant-ph/0102108v2 (Theorem 3, Lemma 1, Theorem 5).
