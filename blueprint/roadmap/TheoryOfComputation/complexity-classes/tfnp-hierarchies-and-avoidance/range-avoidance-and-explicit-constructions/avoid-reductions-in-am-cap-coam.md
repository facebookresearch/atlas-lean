# Ghentiyala–Li–Stephens-Davidowitz: problems reducible to Avoid lie in AM ∩ coAM, so NP-hard Avoid collapses PH

$\mathrm{BPP}^{\mathrm{Avoid}}\subseteq\mathrm{AM}\cap\mathrm{coAM}$ and $\mathrm{prBPP}^{\mathrm{Avoid}}\subseteq\mathrm{prAM}\cap\mathrm{prcoAM}$, even when the reduction is randomized and makes many adaptive queries to Avoid with stretch $m=n+1$. Consequently, if Avoid is $\mathrm{NP}$-hard under such reductions then $\mathrm{coNP}\subseteq\mathrm{AM}$ and the polynomial hierarchy collapses. Also Avoid $\in\mathrm{SearchAMA}$, and, assuming PRGs that fool circuits with parallel $\mathrm{NP}$ gates, there is a single problem $T\in\mathrm{TFNP}$ such that for every $\varepsilon\ge 1/\mathrm{poly}(n)$ Avoid reduces to $T$ by a one-query randomized reduction succeeding with probability $1-\varepsilon$.

In contrast, the related problem in which the circuit maps $2^n-1$ points into $\{0,1\}^n$ (one more hole than pigeons) is $\mathrm{NP}$-hard.

## Proof sketch

The search protocol: Arthur picks random $y$; Merlin may claim a preimage, which Arthur checks, and otherwise the image-size upper bound protocol certifies that a random $y$ is a non-image with high probability, so Arthur's answers to the oracle queries can be trusted. Simulating the reduction with this protocol and its complement places the decision problem in $\mathrm{AM}\cap\mathrm{coAM}$; the collapse follows from the Boppana–Håstad–Zachos theorem.

## Depends on

- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../time-and-space-complexity-classes/am.md)
- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [The polynomial hierarchy](../../time-and-space-complexity-classes/ph.md)

## Proof depends on

- [Ghentiyala–Li–Stephens-Davidowitz: an AM protocol upper-bounding the image size of a circuit](am-protocol-upper-bound-image-size.md)
- [Collapse of the polynomial hierarchy to a level](../../polynomial-hierarchy/collapse-of-the-polynomial-hierarchy-to-a-level.md)
- [AM is contained in $\Pi_2^p$ (Babai)](../../../randomized-and-quantum-complexity/arthur-merlin-and-merlin-arthur-classes/am-subset-pi2.md)

## Sources

- Surendra Ghentiyala, Zeyong Li and Noah Stephens-Davidowitz, "Range avoidance, Arthur-Merlin, and TFNP", ECCC TR25-210 (2025).
