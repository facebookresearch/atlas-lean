# Approximate degree of a Boolean function

For $f : \{0,1\}^n \to \{0,1\}$ and $0 \le \varepsilon < 1/2$, the *$\varepsilon$-approximate degree* $\widetilde{\deg}_\varepsilon(f)$ is the least degree of a real multilinear polynomial $p$ with $|p(x) - f(x)| \le \varepsilon$ for every $x \in \{0,1\}^n$; $\widetilde{\deg}(f) = \widetilde{\deg}_{1/3}(f)$. It satisfies $\widetilde{\deg}_\varepsilon(f) \le \deg(f) \le n$, and $\widetilde{\deg}_0 = \deg$.

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)
- [Multilinear extension](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/multilinear-extension.md)

## Sources

- N. Nisan and M. Szegedy, "On the Degree of Boolean Functions as Real Polynomials", Computational Complexity 4(4), 1994.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
