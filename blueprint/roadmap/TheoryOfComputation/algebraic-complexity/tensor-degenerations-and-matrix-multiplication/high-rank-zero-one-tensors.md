# Coordinate-factoring rank bounds and high-rank 0-1 tensors

(i) An order-three tensor that factors on its first two legs through finite sets $Y_0,Y_1$ has rank at most $|Y_0|\cdot|Y_1|$. (ii) Over every field $K$ and for index sets of sizes $n_0,n_1,n_2$, some $0$–$1$ tensor (indicator of a subset of $X_0\times X_1\times X_2$) has rank greater than $r$ whenever $2^{n_0n_1n_2}$ exceeds the number of $0$–$1$ patterns realizable by rank-$r$ tensors, which is at most $2^{O(r(n_0+n_1+n_2)\log(n_0n_1n_2))}$; so most $0$–$1$ tensors have rank $\Omega(n^2/\log n)$ when $n_0=n_1=n_2=n$.

## Proof sketch

(i) Sum over the $|Y_0||Y_1|$ values of the factored coordinates. (ii) A rank-$r$ tensor whose entries are $0/1$ is determined by the sign pattern of polynomially many polynomials of bounded degree in its $r(n_0+n_1+n_2)$ parameters; Warren/Milnor-type bounds on the number of zero patterns, or multilinear interpolation over the Boolean cube, bound the count.

## Depends on

- [Tensor restrictions and degenerations](tensor-restrictions-and-degenerations.md)

## Sources

- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
- Rafael Pass, "Matrix Multiplication from Polynomial Packings: A Constructive and Elementary Proof of \omega \le 9/4", 2026.
