# ETH implies the Parameterized Inapproximability Hypothesis

The Exponential Time Hypothesis implies PIH: no algorithm decides $\frac{1}{9600}$-Gap $k$-CSP in time $f(k)\cdot n^{o(\sqrt{\log\log k})}$, the first derivation of PIH from a gap-free assumption.

Use ETH in the form: no algorithm decides 3SAT on $n$ variables in time $2^{o(n)}$, even when every variable occurs in at most four clauses and every clause has exactly three distinct variables (equivalent to ETH by sparsification and Tovey's reduction). Then:

1. ETH implies PIH.
2. Quantitatively, assuming ETH, no algorithm decides $\frac{1}{9600}$-Gap $k$-CSP within time $f(k)\cdot n^{o(\sqrt{\log\log k})}$ for any computable $f$.
3. (Parameterized PCP.) For every integer $k\ge 1$, 3SAT has a PCP verifier that can be constructed in time $f(k)\cdot|\Sigma|^{O(1)}$ for a computable $f$, makes two queries to a proof of length $2^{2^{O(k^2)}}$ over an alphabet of size $|\Sigma|=2^{O(n/k)}$, and has perfect completeness and soundness $1-\frac{1}{9600}$.

Consequently, assuming ETH, no FPT algorithm decides $(k,\rho k)$-Exact Cover for any constant $\rho\ge 1$, and for some $\rho\in(1,2)$ no FPT algorithm decides $(k,\rho k)$-Directed Odd Cycle Transversal.

## Expansion

The first reduction maps 3SAT to an ETH-hard vector-valued CSP with $k$ variables taking values in $\mathbb{F}^d$, whose constraints are either linear or of a special parallel structure. The second reduction splits the instance and designs, for each part, a parallel PCP of proximity based on the parallel Walsh–Hadamard code, which checks a family of linear or parallel constraints with constant soundness; parallel constraints are tested through quadratic equations encoded by Walsh–Hadamard codewords. Composing these verifiers and turning them into a 2CSP yields constant gap with only an FPT blow-up in the number of variables.

## Depends on

- [Parameterized Inapproximability Hypothesis](parameterized-inapproximability-hypothesis.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../../../fine-grained-complexity/fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Proof depends on

- [Hadamard tester for systems of quadratic equations](../../../pcp-and-inapproximability/dinur-proof-components/hadamard-tester-for-quadratic-equations.md)
- [FPT-reductions](../../../complexity-classes/parameterized-complexity/fptreduces.md)

## Sources

- Venkatesan Guruswami, Bingkai Lin, Xuandi Ren, Yican Sun and Kewen Wu, "Parameterized Inapproximability Hypothesis under ETH", *Proceedings of the 56th ACM Symposium on Theory of Computing (STOC 2024)*, 2024, https://doi.org/10.1145/3618260.3649644 (Theorems 1.2 and 1.3, Corollaries 1.4 and 1.6, Hypothesis 2.3, Theorems 3.1 and 3.2, Section 3; numbering of the ECCC Report TR23-188 edition read).
