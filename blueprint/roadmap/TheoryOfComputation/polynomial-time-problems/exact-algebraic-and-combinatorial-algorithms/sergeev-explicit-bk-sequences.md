# Sergeev's explicit B_k-sequences are polynomial-time constructible

A **$B_k$-sequence** is a set of positive integers all of whose sums of $k$ elements (with repetition) are distinct as multisets. Sergeev's explicit sequence $H[n,k]$ of $n$ integers, defined through discrete logarithms base $5$ modulo powers of two, is a $B_k$-sequence whose elements have $O(k\log n)$ bits, and it is computable from $n$ and $k$ (in unary) in time $(n+k)^{O(1)}$; in particular the discrete logarithm base $5$ modulo $2^{m}$ is polynomial-time computable.

## Proof sketch

The group $(\mathbb{Z}/2^{m})^{\times}$ is $\{\pm1\}\times\langle5\rangle$, and the discrete logarithm base $5$ is computed bit by bit by lifting from $2^{j}$ to $2^{j+1}$; the construction then needs only polynomially many such logarithms and arithmetic on $O(k\log n)$-bit numbers.

## Depends on

- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- Igor S. Sergeev, "An Explicit Finite B_k-Sequence", arXiv:2304.03988, 2023.
