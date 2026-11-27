# Forrelation of two Boolean functions

For $f, g : \{0,1\}^n \to \{\pm 1\}$ and $N = 2^n$, the *forrelation* is

$$
\Phi(f, g) = \frac{1}{N^{3/2}} \sum_{x, y \in \{0,1\}^n} f(x) (-1)^{x \cdot y} g(y) = \frac{1}{\sqrt N}\sum_{y} \hat f(y)\, g(y),
$$

where $\hat f(y) = N^{-1}\sum_x f(x)(-1)^{x\cdot y}$; it measures the correlation of $g$ with the Fourier transform of $f$ and satisfies $|\Phi(f,g)| \le 1$. The *Forrelation problem* is the promise problem of deciding whether $|\Phi(f,g)| \le 1/100$ or $\Phi(f,g) \ge 3/5$, given oracle access to $f$ and $g$.

## Sources

- Scott Aaronson, Andris Ambainis, "Forrelation: a problem that optimally separates quantum from classical computing", SIAM Journal on Computing 47(3) (2018), STOC (2015); arXiv:1411.5729.
- Scott Aaronson, Andris Ambainis, "The need for structure in quantum speedups", Theory of Computing 10 (2014); arXiv:0911.0996.
