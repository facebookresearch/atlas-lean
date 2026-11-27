# Integer multilinear interpolation on consecutive Hamming layers

For integers $k\ge0$, $t\ge1$ and any prescribed integers $v_k,\dots,v_{k+t-1}$, there is a multilinear polynomial $p\in\mathbb{Z}[x_1,\dots,x_n]$ with integer coefficients and of total degree at most $t-1$ with $p(x)=v_{|x|}$ for every $x\in\{0,1\}^n$ with $k\le|x|<k+t$; it is an integer combination of elementary symmetric polynomials, so it can be read over every field.

## Proof sketch

On $\{0,1\}^n$, $e_j(x)=\binom{|x|}{j}$. Interpolate the univariate function $w\mapsto v_w$ on the $t$ consecutive integers $k,\dots,k+t-1$ by a polynomial of degree at most $t-1$; an integer-valued polynomial on $t$ consecutive integers is integer-valued on $\mathbb{Z}$ and so has integer coordinates in the binomial basis $\binom{w}{j}$, and substituting $e_j$ for $\binom wj$ gives $p$.

## Depends on

- [Multilinear extension](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/multilinear-extension.md)

## Sources

- Josh Alman, Ryan Williams, "Probabilistic Rank and Matrix Rigidity", 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 2017 (arXiv:1611.05558), Lemma 3.2.
