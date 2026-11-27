# Abboud–Fischer–Kelley–Lovett–Meka: combinatorial Boolean matrix multiplication in n^3/2^{Ω((log n)^{1/7})} time

There is a deterministic combinatorial algorithm computing the Boolean product of two $n\times n$ Boolean matrices in time

$$
\frac{n^3}{2^{\Omega((\log n)^{1/7})}},
$$

a superpolylogarithmic speed-up over cubic time; previous combinatorial algorithms saved only polylogarithmic factors ($\log^2 n$ by Arlazarov et al., then $\log^{2.25}n$, $\log^3 n$ and $\log^4 n$ by Bansal–Williams, Chan and Yu). The **combinatorial BMM hypothesis** (stated as a hypothesis, popular since the 1990s and the basis of many conditional lower bounds) asserts that no combinatorial algorithm runs in $O(n^{3-\varepsilon})$ time for any $\varepsilon > 0$; the result does not refute it, but rules out the stronger form excluding all superpolylogarithmic savings. The same saving applies to triangle detection and to problems reducible to BMM. Algebraic algorithms achieve $O(n^{\omega})$ with $\omega < 3$, starting with Strassen.

## Proof sketch

By the subcubic equivalence of Vassilevska Williams and Williams it suffices to detect triangles. Decompose the bipartite graphs between layers into grid-regular pieces; if two pieces sharing the middle layer are both grid-regular and dense, their product is nearly uniform, so either the third piece is very sparse (handled directly) or a triangle must exist and is found quickly. Sparse pieces are handled by brute force, and the quasipolynomial number of pieces yields the $2^{\Omega((\log n)^{1/7})}$ saving.

## Proof depends on

- [Abboud–Fischer–Kelley–Lovett–Meka: efficient grid-regularity decomposition with quasipolynomially many parts](afklm-grid-regularity-decomposition.md)
- [Strassen's 1969 bound on the matrix multiplication exponent](../../algebraic-complexity/matrix-multiplication-exponent/strassen1969-upper.md)
- [Grid norms and grid regularity of Boolean matrices (Kelley–Lovett–Meka)](grid-norms-and-grid-regularity.md)

## Sources

- Amir Abboud, Nick Fischer, Zander Kelley, Shachar Lovett and Raghu Meka, "New Graph Decompositions and Combinatorial Boolean Matrix Multiplication Algorithms", STOC (2024), arXiv:2311.09095.
- Virginia Vassilevska Williams and R. Ryan Williams, "Subcubic Equivalences Between Path, Matrix, and Triangle Problems", Journal of the ACM 65(5) (2018).
