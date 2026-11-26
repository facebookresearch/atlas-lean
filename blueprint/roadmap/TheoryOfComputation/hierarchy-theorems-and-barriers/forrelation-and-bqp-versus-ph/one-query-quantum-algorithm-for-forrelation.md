# A one-query quantum algorithm estimating forrelation

There is a quantum algorithm making one query to $f$ and one to $g$ (or a single query to the combined oracle) and using $O(\log N)$ additional gates whose acceptance probability is exactly $\frac{1 + \Phi(f, g)}{2}$.

## Proof sketch

Prepare $N^{-1/2}\sum_x |x\rangle$, apply the phase oracle for $f$, apply $H^{\otimes n}$, apply the phase oracle for $g$, and perform a Hadamard test of the resulting state against the uniform superposition. The overlap equals $N^{-3/2}\sum_{x,y} f(x)(-1)^{x\cdot y}g(y) = \Phi(f,g)$, so the test accepts with probability $(1 + \Phi)/2$.

## Depends on

- [Forrelation of two Boolean functions](forrelation-of-two-boolean-functions.md)

## Sources

- Scott Aaronson, Andris Ambainis, "Forrelation: a problem that optimally separates quantum from classical computing", SIAM Journal on Computing 47(3) (2018), STOC (2015); arXiv:1411.5729.
