# Hadamard matrices have rigidity at least n^2/(4r)

Let $H$ be an $n\times n$ Hadamard matrix ($\pm1$ entries with $HH^{T}=nI$) or a generalized Hadamard matrix over $\mathbb{C}$ (entries of modulus one, $HH^{\ast}=nI$). Then for $1\le r\le n/2$, $n^2\le4r\,R_H(r)$, i.e. $R_H(r)\ge n^2/(4r)$. For the $2^k\times2^k$ Sylvester–Hadamard matrix the bound $2^{2k}\le4r\,R(r)$ holds over every field of characteristic not two, for $r=2^t\le2^{k-1}$.

## Proof sketch

Every $a\times b$ submatrix of a Hadamard matrix has rank at least $ab/n$ (its rows are orthogonal of norm $\sqrt n$, so the operator norm is at most $\sqrt n$ while the Frobenius norm is $\sqrt{ab}$). If fewer than $n^2/(4r)$ entries are changed, some $2r$ rows contain few changes, and selecting $2r$ rows and the unchanged columns gives a submatrix of rank above $r$. For Sylvester matrices with $r=2^t$, tile by the $(2^k/2r)^2$ blocks of size $2r\times2r$, each $\pm S_{t+1}$ of rank $2r$; each changed entry lowers the rank of its block by at most one, so lowering the rank to $r$ needs at least $r$ changes in every block (Midrijānis).

## Depends on

- [Matrix rigidity](matrix-rigidity.md)
- [Hadamard matrix](../../../LinearAlgebra/special-matrices/hadamard-matrices/is-hadamard-matrix.md)

## Sources

- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
- Ronald de Wolf, "Lower Bounds on Matrix Rigidity via a Quantum Argument", Automata, Languages and Programming (ICALP 2006), Part I, 2006.
- Gatis Midrijānis, "Three lines proof of the lower bound for the matrix rigidity", 2005.
