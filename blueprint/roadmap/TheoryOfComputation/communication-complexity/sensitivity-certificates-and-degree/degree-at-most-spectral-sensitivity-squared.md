# Degree is at most the square of spectral sensitivity

For every Boolean function $f$, $\deg(f) \le \lambda(f)^2$; more precisely, if $\hat f(S) \ne 0$ then $\sqrt{|S|} \le \lambda(f)$. Since $\lambda(f) \le s(f)$, this implies Huang's theorem $\deg(f) \le s(f)^2$.

## Proof sketch

Restrict to the subcube of coordinates $S$ with the others fixed so that the restriction has full degree $|S|$. Huang's signed adjacency matrix on that subcube has eigenvalues $\pm\sqrt{|S|}$, each with multiplicity $2^{|S|-1}$; the function $(-1)^{f}\chi_S$ splits the subcube so that a Cauchy interlacing argument applied to the sensitivity graph (entrywise dominated by the signed matrix) gives $\lambda \ge \sqrt{|S|}$.

## Depends on

- [Sensitivity graph and spectral sensitivity](spectral-sensitivity.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Proof depends on

- [Huang's sensitivity theorem](../query-and-communication-measures/huang-s-sensitivity-theorem.md)

## Sources

- H. Huang, "Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture", Annals of Mathematics 190(3), 2019.
- S. Aaronson, S. Ben-David, R. Kothari, S. Rao and A. Tal, "Degree vs. Approximate Degree and Quantum Implications of Huang's Sensitivity Theorem", STOC 2021.
