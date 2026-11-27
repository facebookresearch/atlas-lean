# Brown's unit-sphere matrix is 3-free

Let $p\equiv3\pmod4$ be prime and $V=(\mathbb{Z}/p\mathbb{Z})^3$. The $p^3\times p^3$ Boolean matrix $A$ with $A_{u,v}=1$ iff $(u_1-v_1)^2+(u_2-v_2)^2+(u_3-v_3)^2=1$ has exactly $p^2-p$ ones in each row, total weight $p^4(p-1)$, and contains no $3\times3$ all-ones submatrix. Thus $A$ is a $3$-free matrix of weight $\Theta(m^{5/3})$, where $m=p^3$.

## Proof sketch

The unit sphere around a point of $\mathbb{F}_p^3$ has $p^2-p$ points when $-1$ is a non-residue. Three unit spheres around distinct centers $a,b,c$ meet in at most two points. Subtracting the equations gives the planes $2(b-a)\cdot x=|b|^2-|a|^2$ and $2(c-a)\cdot x=|c|^2-|a|^2$. If they meet in a line, that line meets the sphere in at most two points unless it lies on it; a line $y+\lambda d$ lies on the unit sphere only if $d\cdot d=0$, $y\cdot d=0$ and $y\cdot y=1$, and on $d^\perp$ the form takes only values in $-1$ times squares, which excludes $y\cdot y=1$ because $-1$ is a non-residue for $p\equiv 3\pmod 4$. If the planes are parallel and distinct the intersection is empty; they coincide only when the centers are collinear with an isotropic direction $d=b-a$, and then the common points satisfy $|x-a|^2=1$ with $x-a\perp d$, which again has no solution for the same reason.

## Depends on

- [k-free (rectangle-free) Boolean matrices](k-free-boolean-matrices.md)

## Sources

- William G. Brown, "On Graphs That Do Not Contain a Thomsen Graph", Canadian Mathematical Bulletin 9(3), 281–285, 1966.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012 (Brown's construction with $d$ a quadratic residue for $p\equiv 3 \pmod 4$).
