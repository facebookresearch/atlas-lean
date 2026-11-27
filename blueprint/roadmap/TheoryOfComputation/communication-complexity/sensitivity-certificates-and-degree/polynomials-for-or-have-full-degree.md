# Polynomials agreeing with OR on the cube have full degree

For $n \ge 1$, the unique multilinear polynomial $p \in \mathbb{R}[x_1, \dots, x_n]$ with $p(x) = \mathrm{OR}(x)$ for every $x \in \{0,1\}^n$ is $1 - \prod_{i=1}^n (1 - x_i)$, so the degree of OR is $n$: $\deg(\mathrm{OR}_n) = n$.

## Proof sketch

Expanding $1 - \prod_i (1 - x_i)$ gives the monomial $x_1 \cdots x_n$ with coefficient $(-1)^{n+1}$, and the representation is unique (multilinear interpolation on the cube).

Derived here (not stated in the cited sources): the same holds over every nontrivial commutative ring $R$ and for every polynomial, multilinear or not. Reducing $p \in R[x_1, \dots, x_n]$ modulo the relations $x_i^2 = x_i$ yields a multilinear polynomial of no larger degree that still agrees with OR on $\{0,1\}^n$; multilinear interpolation on the cube is unique over any commutative ring (Möbius inversion over subsets), so this reduction equals $1 - \prod_i (1 - x_i)$, whose top coefficient $\pm 1$ is nonzero whenever $1 \ne 0$. In particular OR has exact degree $n$ over $\mathbb{F}_q$ for every prime $q$.

## Depends on

- [Multilinear extension](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/multilinear-extension.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009; web draft of January 2007, Definition 11.22, Example 11.23 and the sentence after it ("The degree of AND and OR is n").
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002, Section 4.3, Definitions 3 and 4, and Sections 4.4 and 5.3 ("deg(OR_n) = n").
- R. Smolensky, "Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity", STOC 1987.
