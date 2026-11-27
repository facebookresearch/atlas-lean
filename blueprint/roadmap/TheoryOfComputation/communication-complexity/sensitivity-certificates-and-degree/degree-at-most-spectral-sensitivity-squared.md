# Degree is at most the square of spectral sensitivity

For every Boolean function $f$, $\deg(f) \le \lambda(f)^2$; more precisely, if $\hat f(S) \ne 0$ then $\sqrt{|S|} \le \lambda(f)$. Since $\lambda(f) \le s(f)$, this implies Huang's theorem $\deg(f) \le s(f)^2$.

## Proof sketch

For $S = \varnothing$ there is nothing to prove. Otherwise replace $S$ by an inclusion-maximal $T \supseteq S$ with $\hat f(T) \ne 0$, so $|T| \ge |S|$; by the face lemma every restriction to a face parallel to $T$ has full degree $d = |T|$, and its sensitivity graph is an induced subgraph of $G_f$, so its spectral norm is at most $\lambda(f)$. So assume $f$ has full degree $d$ on $\{0,1\}^d$. Let $V_0$ be the inputs where $f$ agrees with parity and $V_1$ the rest; $|V_0| \ne |V_1|$ because the top coefficient is nonzero, say $|V_0| \ge 2^{d-1} + 1$. Every hypercube edge inside $V_0$ is sensitive. Huang's signed matrix $B$ satisfies $B^2 = d\,I$ and has trace $0$, so its $+\sqrt d$ eigenspace has dimension $2^{d-1} > |V_1|$ and contains a nonzero eigenvector $v$ vanishing on $V_1$. With $v' = |v|$ entrywise, for $x \in V_0$ one has $(A_f v')_x \ge \sum_{y \sim x,\, y \in V_0} |v_y| \ge |(Bv)_x| = \sqrt d\, v'_x$, since $|B| \le A_f$ entrywise on $V_0$; so $\|A_f v'\| \ge \sqrt d\,\|v'\|$ and $\lambda(f) \ge \sqrt d$. (The sensitivity adjacency is not entrywise dominated by the signed matrix on the whole cube; the comparison is made only on $V_0$.)

## Depends on

- [Sensitivity graph and spectral sensitivity](spectral-sensitivity.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Proof depends on

- [Faces parallel to a maximal Fourier support are nonconstant](faces-parallel-to-maximal-fourier-support.md)
- [Huang's sensitivity theorem](../query-and-communication-measures/huang-s-sensitivity-theorem.md)

## Sources

- H. Huang, "Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture", Annals of Mathematics 190(3), 2019.
- S. Aaronson, S. Ben-David, R. Kothari, S. Rao and A. Tal, "Degree vs. Approximate Degree and Quantum Implications of Huang's Sensitivity Theorem", STOC 2021 (Theorem 1 and its proof in Section 3).
