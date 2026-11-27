# Williams: split-and-list transfer from orthogonal vectors to SAT

If Orthogonal Vectors on $N$ vectors of dimension $d$ can be decided in time $N^{2-\varepsilon}\mathrm{poly}(d)$ for some $\varepsilon>0$, then CNF-SAT on $n$ variables and $m$ clauses can be decided in time $2^{(1-\min(\varepsilon,1)/2)n}\mathrm{poly}(n,m)$, contradicting SETH.

## Proof sketch

Split the variables into halves and list the $2^{n/2}$ assignments of each half; map an assignment to the $0/1$ vector over clauses marking the clauses it does **not** satisfy. A pair of half-assignments satisfies $\varphi$ iff their vectors are orthogonal; this is an OV instance with $N=2^{n/2}$ and $d=m$, built in time $2^{n/2}\mathrm{poly}(n,m)$. (Williams states it as a cooperative subset-query problem, equivalent to OV.)

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Sources

- Ryan Williams, "A New Algorithm for Optimal 2-Constraint Satisfaction and Its Implications", Theoretical Computer Science 348(2–3), 2005, Theorem 5.1 and the Orthogonal Vectors formulation after it.
