# The inner-product matrix has full rank

The sign matrix $H$ of the inner product modulo two on $\{0,1\}^n$, with entries $(-1)^{\langle x, y \rangle}$, satisfies $H^2 = 2^n I$, so it is a Hadamard matrix of full rank $2^n$ over any field of characteristic not $2$. The $0/1$ communication matrix of the inner product has rank exactly $2^n - 1$ over such fields, and every protocol computing it has at least $2^n - 1$ leaves labelled $1$.

## Proof sketch

Character orthogonality gives $\sum_y (-1)^{\langle w, y\rangle} = 2^n [w = 0]$, hence $H^2 = 2^n I$. The $0/1$ matrix is $(J - H)/2$ with $J$ the all-ones matrix, so its rank is at least $2^n - 1$, and it is at most $2^n - 1$ because the row of $x = 0$ is zero. The leaf count follows from the rank bound: the $1$-leaves of a protocol tile the ones of the matrix.

## Depends on

- [Communication matrix](../deterministic-communication-protocols/comm-matrix.md)
- [Fourier character on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/cube-chi.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
