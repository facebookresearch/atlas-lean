# OR-complexity of a matrix and its complement can differ polynomially

There are explicit $n\times n$ Boolean matrices $C$ (for infinitely many $n$, namely $n=\binom{p^3}{2}$ for primes $p\equiv3\pmod 4$) such that $\mathrm{OR}(C)\le\mathrm{OR}_3(C)\le 7n$ while the complement $\bar C$ is $2$-free and $\mathrm{OR}(\bar C)=|\bar C|=\Omega(n^{4/3})$; explicitly $n^4\le2^{23}\,\mathrm{OR}(\bar C)^3$.

## Proof sketch

Take $C$ to be the complement of the $2$-rectangle lift of Brown's $3$-free matrix. The complement of a lift has a depth-$3$ circuit of linear size built from row-pair and column-pair gadgets. The lift of a $3$-free matrix is $2$-free and, by the rectangle count, has weight $\Omega(n^{4/3})$, so Nechiporuk's bound gives $\mathrm{OR}(\bar C)=|\bar C|$.

## Depends on

- [Rectifier (OR) circuits for Boolean matrices](rectifier-or-circuits.md)

## Proof depends on

- [Dense Boolean matrices contain many 2-rectangles, and the 2-rectangle lift](dense-matrices-contain-many-two-rectangles.md)
- [Brown's unit-sphere matrix is 3-free](brown-unit-sphere-matrix.md)
- [Nechiporuk's lower bound for rectifier circuits of k-free matrices](nechiporuk-rectifier-lower-bound.md)

## Sources

- Igor S. Sergeev, "On Relative OR-Complexity of Boolean Matrices and Their Complements", 2014.
- William G. Brown, "On Graphs That Do Not Contain a Thomsen Graph", Canadian Mathematical Bulletin, 1966.
