# Chen–Huang–Li–Ren: slightly non-trivial Satisfying-Pairs algorithms give FP^NP algorithms for Avoid and Remote Point

For a circuit class $\mathcal{C}$, the **$\mathcal{C}$-Satisfying-Pairs** problem gets circuits $C_1,\dots,C_a\in\mathcal{C}$ and inputs $x_1,\dots,x_b$ and asks to (approximately) count the pairs $(i,j)$ with $C_i(x_j)=1$. A slightly non-trivial algorithm for $\mathcal{C}$-Satisfying-Pairs yields $\mathrm{FP}^{\mathrm{NP}}$ algorithms for $\mathcal{C}$-Avoid, for its average-case analogue $\mathcal{C}$-RemotePoint, and for $\mathcal{C}$-AvgPartialHard.

## Proof sketch

This strengthens the Ren–Santhanam–Wang framework: a short, smooth and rectangular PCP of proximity reduces checking that a candidate string is far from every output to a Satisfying-Pairs instance between verifier circuits and proof positions, and the $\mathrm{NP}$ oracle constructs the candidate bit by bit while the faster count certifies progress.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)

## Proof depends on

- [Ren–Santhanam–Wang: FP^NP algorithms for C-Avoid from circuit-analysis data structures](rsw-avoid-from-circuit-analysis.md)

## Sources

- Yeyuan Chen, Yizhi Huang, Jiatu Li and Hanlin Ren, "Range Avoidance, Remote Point, and Hard Partial Truth Tables via Satisfying-Pairs Algorithms", STOC (2023), ECCC TR23-072.
