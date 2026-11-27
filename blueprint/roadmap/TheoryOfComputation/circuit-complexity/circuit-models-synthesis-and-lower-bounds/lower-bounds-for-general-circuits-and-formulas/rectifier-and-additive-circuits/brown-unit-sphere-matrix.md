# Brown's unit-sphere matrix is 3-free

Let $p\equiv3\pmod4$ be prime and $V=(\mathbb{Z}/p\mathbb{Z})^3$. The $p^3\times p^3$ Boolean matrix $A$ with $A_{u,v}=1$ iff $(u_1-v_1)^2+(u_2-v_2)^2+(u_3-v_3)^2=1$ has exactly $p^2-p$ ones in each row, total weight $p^4(p-1)$, and contains no $3\times3$ all-ones submatrix. Thus $A$ is a $3$-free matrix of weight $\Theta(m^{5/3})$, where $m=p^3$.

## Proof sketch

The unit sphere around a point of $\mathbb{F}_p^3$ has $p^2-p$ points when $-1$ is a non-residue. Three spheres around three distinct centers meet in at most two points: subtracting the equations reduces to the intersection of a line (the common radical line) with a sphere, and three points on a sphere are not collinear.

## Depends on

- [k-free (rectangle-free) Boolean matrices](k-free-boolean-matrices.md)

## Sources

- William G. Brown, "On Graphs That Do Not Contain a Thomsen Graph", Canadian Mathematical Bulletin, 1966.
