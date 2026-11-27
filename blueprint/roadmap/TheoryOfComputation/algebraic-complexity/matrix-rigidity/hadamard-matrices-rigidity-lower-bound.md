# Hadamard matrices have rigidity at least n^2/(4r)

Let $H$ be an $n\times n$ Hadamard matrix ($\pm1$ entries with $HH^{T}=nI$), with rigidity taken over the reals. Then for $1\le r\le n/2$, $R_H(r)\ge n^2/(4r)$, i.e. $n^2\le4r\,R_H(r)$. The same bound holds for generalized Hadamard matrices, the orthogonal matrices all of whose entries have the same magnitude.

## Proof sketch

Every $a\times b$ submatrix of a Hadamard matrix has rank at least $ab/n$ (its rows are orthogonal of norm $\sqrt n$, so the operator norm is at most $\sqrt n$ while the Frobenius norm is $\sqrt{ab}$). If fewer than $n^2/(4r)$ entries are changed, some $2r$ rows contain few changes, and selecting $2r$ rows and the unchanged columns gives a submatrix of rank above $r$. For the $2^k\times2^k$ Sylvester–Hadamard matrix and $r=2^t\le2^{k-1}$ there is a shorter argument (Midrijānis): tile by the $(2^k/2r)^2$ blocks of size $2r\times2r$, each $\pm S_{t+1}$ of rank $2r$; each changed entry lowers the rank of its block by at most one, so lowering the rank to $r$ needs at least $r$ changes in every block. (Derived, not stated by the sources: since the blocks $S_{t+1}$ have determinant a power of $2$ up to sign, the Sylvester bound $2^{2k}\le4r\,R(r)$ holds over every field of characteristic not two.)

## Depends on

- [Matrix rigidity](matrix-rigidity.md)
- [Hadamard matrix](../../../LinearAlgebra/special-matrices/hadamard-matrices/is-hadamard-matrix.md)

## Sources

- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
- Ronald de Wolf, "Lower Bounds on Matrix Rigidity via a Quantum Argument", Automata, Languages and Programming (ICALP 2006), Part I, 2006; arXiv:quant-ph/0505188: Section 1.2 (the bounds hold for all generalized Hadamard matrices), Theorem 1 and Theorem 2, and Section 5.1 (Midrijānis's proof for Sylvester matrices).
- Gatis Midrijānis, "Three lines proof of the lower bound for the matrix rigidity", 2005.
