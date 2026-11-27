# The Hessian of the permanent at the Mignon–Ressayre point

Let $N\ge3$, fix an index $o$, and let $P$ be the $N\times N$ all-ones matrix with the entry at $(o,o)$ replaced by $1-N$. Then $\mathrm{per}(P)=0$, and the Hessian of the generic permanent at $P$, indexed by pairs of entries $(r,c),(r',c')$, equals $(N-2)!\,[r\ne r'][c\ne c']-N(N-3)!\,[r,r',o\text{ distinct}][c,c',o\text{ distinct}]$. Over a field of characteristic zero this $N^2\times N^2$ matrix has full rank $N^2$.

## Proof sketch

Compute second partial derivatives as permanents of $(N-2)\times(N-2)$ submatrices of $P$, which are all-ones matrices possibly containing the special entry; the Hessian is a combination $p(J-I)\otimes(J-I)+s(D(J-I)D)\otimes(D(J-I)D)$ of Kronecker products whose eigenvalues are computed explicitly and are nonzero.

## Depends on

- [Permanent of an encoded 0-1 matrix](../../counting-complexity/complexity-of-the-permanent/perm-fun.md)

## Sources

- Thierry Mignon, Nicolas Ressayre, "A quadratic bound for the determinant and permanent problem", International Mathematics Research Notices, 2004.
