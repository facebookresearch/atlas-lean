# Parameterized Inapproximability Hypothesis

The Parameterized Inapproximability Hypothesis asserts that no fixed-parameter tractable algorithm can distinguish a satisfiable binary CSP with $k$ variables from one in which every assignment violates an $\varepsilon$ fraction of the constraints; it plays the role of the PCP theorem in parameterized complexity.

A CSP instance of arity two is $G=(V,E,\Sigma,\{\Pi_e\}_{e\in E})$: variables $V$, constraints $E$ on pairs of distinct variables (parallel constraints allowed), alphabet $\Sigma$, and validity functions $\Pi_e:\Sigma\times\Sigma\to\{0,1\}$; its size is $|G|=(|V|+|E|)\cdot|\Sigma|$. For an assignment $\sigma:V\to\Sigma$,

$$
\mathrm{val}(G,\sigma)=\frac{1}{|E|}\sum_{e\in E}\Pi_e(\sigma(u_e),\sigma(v_e)),\qquad\mathrm{val}(G)=\max_{\sigma}\mathrm{val}(G,\sigma).
$$

The parameter is $k=|V|$, and an algorithm is fixed-parameter tractable if it runs in time $f(k)\cdot n^{O(1)}$ with $n=|G|$ and $f$ computable. The promise problem $\varepsilon$-Gap $k$-CSP asks to decide whether $\mathrm{val}(G)=1$ or $\mathrm{val}(G)<1-\varepsilon$.

**Hypothesis (PIH).** There is an absolute constant $0<\varepsilon<1$ such that no FPT algorithm decides $\varepsilon$-Gap $k$-CSP.

This is the reformulation by Feldmann, Karthik, Lee and Manurangsi of the hypothesis of Lokshtanov, Ramanujan, Saurabh and Zehavi, which asked for $\mathsf{W}[1]$-hardness instead of FPT-intractability. The constant $\varepsilon$ is unimportant: standard reductions boost it to $1-\eta$ for any constant $\eta>0$.

## Expansion

PIH is the common starting point for parameterized inapproximability of $k$-Clique, $k$-Set Cover, $k$-Exact Cover, Shortest Vector, Directed Odd Cycle Transversal, Determinant Maximization, Grid Tiling and $k$-Max Cover. It follows easily from Gap-ETH, whose built-in gap allows a gap-preserving reduction; the difficulty is to derive it from a hypothesis without a gap.

## Depends on

- [Fixed-parameter tractable problems](fpt.md)
- [2CSP instances](../../pcp-and-inapproximability/dinur-s-gap-amplification/cspinstance.md)

## Proof depends on

None.

## Sources

- Venkatesan Guruswami, Bingkai Lin, Xuandi Ren, Yican Sun and Kewen Wu, "Parameterized Inapproximability Hypothesis under Exponential Time Hypothesis", *Proceedings of the 56th ACM Symposium on Theory of Computing (STOC 2024)*, 2024, pp. 24–35, https://doi.org/10.1145/3618260.3649771 (Hypothesis 1.1, Section 2.1 and Hypothesis 2.1; numbering of the ECCC Report TR23-188 edition read, titled "Parameterized Inapproximability Hypothesis under ETH").
