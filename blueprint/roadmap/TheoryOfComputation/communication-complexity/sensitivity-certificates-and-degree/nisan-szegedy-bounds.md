# Nisan–Szegedy: block sensitivity is at most quadratic in degree and approximate degree

For every Boolean function $f$, $bs(f) \le 2 \deg(f)^2$ and $bs(f) \le 6\, \widetilde{\deg}(f)^2$, where $\widetilde{\deg}(f)$ is the $1/3$-approximate degree.

## Proof sketch

Let $p$ be a real polynomial of degree at most $D$ with $|p(x)-f(x)|\le\varepsilon<1/2$ for all $x$ ($\varepsilon=0$ when $p$ represents $f$), and let $x$ have $b = bs(f)$ disjoint sensitive blocks. Substituting $y \in \{0,1\}^b$ for the blocks gives a polynomial of degree at most $D$ that is near $0$ at $0$ and near $1$ at every unit vector. Minsky–Papert symmetrization yields a univariate polynomial of degree at most $D$, bounded on $\{0, \dots, b\}$, that jumps by at least $1 - 2\varepsilon$ between $0$ and $1$; the Markov brothers' inequality (in the Ehlich–Zeller–Rivlin–Cheney form for integer points) forces $D = \Omega(\sqrt b)$: with $D=\deg(f)$ and $\varepsilon=0$ this gives $bs(f)\le 2\deg(f)^2$, and with $\varepsilon=1/3$ it gives $bs(f)\le 6\,\widetilde{\deg}(f)^2$. Derived here from the same argument, without a separate source, for every $\varepsilon<1/2$: $(1 - 2\varepsilon)\, bs(f) \le 2 D^2$.

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)
- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)
- [Approximate degree of a Boolean function](approximate-degree-of-a-boolean-function.md)

## Proof depends on

- [Minsky–Papert symmetrization](minsky-papert-symmetrization.md)

## Sources

- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002 (Theorems 4 and 7, Definition 5).
