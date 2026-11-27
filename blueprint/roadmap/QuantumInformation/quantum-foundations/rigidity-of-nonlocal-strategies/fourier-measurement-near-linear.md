# Near-linear observables have an almost projective Fourier measurement

Let $A(a)$, $a\in\{0,1\}^n$, be $\pm1$ observables, $\varphi$ a state, and suppose $\mathbb{E}_{a,b}\operatorname{Re}\varphi(A(a)A(b)A(a+b))\ge1-\delta$. Then the Fourier measurement $B$ satisfies

$$
\sum_u\operatorname{Re}\varphi(B_u^2)\ge1-2\delta\qquad\text{and}\qquad\mathbb{E}_a\Big\|A(a)-\sum_u(-1)^{a\cdot u}B_u\Big\|_\varphi^2\le2\delta .
$$

## Proof sketch

Since $\hat A(u)^3\le\hat A(u)^4$ fails in general, use instead that $\sum_u\hat A(u)^2 = 1$ and $-\hat A(u)^2\le\hat A(u)^3\le\hat A(u)^2$ to compare $\sum_u\varphi(\hat A(u)^4)$ with $\sum_u\varphi(\hat A(u)^3)\ge1-\delta$. For the second claim expand the squared distance and use $\mathbb{E}_aA(a)\sum_u(-1)^{a\cdot u}B_u = \sum_u\hat A(u)^3$ and Parseval in the state.

## Depends on

- [Fourier measurement of a family of $\pm1$ observables](fourier-measurement-of-observables.md)
- [States on star-ordered algebras, state-dependent norm and approximation](../states-and-measurements-on-operator-algebras/algebraic-states-and-state-dependent-norm.md)

## Proof depends on

- [Fourier measurement of a family of $\pm1$ observables](fourier-measurement-of-observables.md)

## Sources

- A. Natarajan and T. Vidick, "A quantum linearity test for robustly verifying entanglement", Proceedings of the 49th Annual ACM Symposium on Theory of Computing (STOC 2017), 1003-1015, 2017.
