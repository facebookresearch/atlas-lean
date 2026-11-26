# Integer multilinear interpolation on consecutive Hamming layers

For integers $k\ge0$, $t\ge1$ and any prescribed integers $v_k,\dots,v_{k+t-1}$, there is a multilinear polynomial $p\in\mathbb{Q}[x_1,\dots,x_n]$ of total degree at most $t-1$ with $p(x)=v_{|x|}$ for every $x\in\{0,1\}^n$ with $k\le|x|<k+t$; it is a combination of elementary symmetric polynomials.

## Proof sketch

On $\{0,1\}^n$, $e_j(x)=\binom{|x|}{j}$. Interpolate the univariate function $w\mapsto v_w$ on the $t$ consecutive integers $k,\dots,k+t-1$ by a polynomial of degree at most $t-1$ in the binomial basis $\binom{w}{j}$, and substitute $e_j$ for $\binom wj$.

## Depends on

- [Matrix rigidity](matrix-rigidity.md)
- [Multilinear extension](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/multilinear-extension.md)

## Sources

- Josh Alman, Ryan Williams, "Probabilistic Rank and Matrix Rigidity", 2017.
