# Coordinate index of the tiling cell containing a site

For $d, m, n \in \mathbb{N}$, a site $x \in \mathbb{Z}^d$ and a coordinate $i$, the cell index is $\lfloor \max(x_i + n, 0) / (2m+1) \rfloor$ (negative values of $x_i + n$ are replaced by $0$).
