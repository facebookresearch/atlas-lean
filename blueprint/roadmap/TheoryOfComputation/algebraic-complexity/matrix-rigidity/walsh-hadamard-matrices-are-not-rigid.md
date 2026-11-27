# Alman–Williams: Walsh–Hadamard matrices are not rigid

Let $H_n$ be the $N\times N$ Sylvester–Hadamard (Walsh–Hadamard) matrix, $N=2^n$, indexed by subsets $x,y\subseteq[n]$ with entries $(-1)^{|x\cap y|}$. Over every field, for every sufficiently small $\varepsilon>0$ and every $n$, $R_{H_n}(N^{1-f(\varepsilon)})\le N^{1+\varepsilon}$ with $f(\varepsilon)=\Theta(\varepsilon^2/\log(1/\varepsilon))$; in fact changing at most $N^{\varepsilon}$ entries in each row suffices. Hence for every $\varepsilon>0$ there is $\delta>0$ with $R_{H_n}(N^{1-\delta})\le N^{1+\varepsilon}$.

## Proof sketch

For rows and columns of weight near $n/2$, the sign $(-1)^{|x\cap y|}$ depends only on $|x\cap y|$, which lies in a narrow band for most pairs; interpolate it there by a low-degree multilinear polynomial in the coordinates of $x\cap y$, which defines a matrix of low rank (a sum of rank-one terms indexed by small sets) agreeing with $H_n$ except on few off-band pairs. Rows and columns of atypical weight are corrected separately.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)
- [Hadamard matrix](../../../LinearAlgebra/special-matrices/hadamard-matrices/is-hadamard-matrix.md)

## Proof depends on

- [Integer multilinear interpolation on consecutive Hamming layers](multilinear-interpolation-on-consecutive-layers.md)

## Sources

- Josh Alman, Ryan Williams, "Probabilistic Rank and Matrix Rigidity", 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 2017 (arXiv:1611.05558), Theorem 1.1 and Lemma 3.1.
