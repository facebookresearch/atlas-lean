# MINnKT is in BPP iff NP ⊆ BPP

Computing nondeterministic time-bounded Kolmogorov complexity captures the hardness of NP: MINnKT is in BPP exactly when NP is contained in BPP. This settles Ko's question on the hardness of MINKT in the nondeterministic setting, through a non-black-box argument rather than a Karp reduction.

Assume the computational model is strongly efficient (efficient simulation in both directions, extension of witness and random strings, efficient composition). Then:

1. $\mathrm{MINnKT}\in\mathrm{BPP}\iff\mathrm{NP}\subseteq\mathrm{BPP}$.
2. If $(\mathrm{MINnKT},\mathcal{U})\in\mathrm{AvgBPP}$ for the uniform distribution $\mathcal{U}$, then $\mathrm{DistNP}\subseteq\mathrm{AvgBPP}$.
3. If $(\mathrm{MINnKT},\mathcal{U})\in\mathrm{AvgBPP}$, then $\mathrm{NP}\subseteq\mathrm{RTIME}[2^{O(n/\log n)}]$.
4. For the problem $\mathrm{MINpnKT}$ of computing $\mathrm{pnK}^t$, $\mathrm{MINpnKT}\in\mathrm{prBPP}\iff\mathrm{NP}\subseteq\mathrm{BPP}$.

## Expansion

The easy direction: $\mathrm{MINnKT}\in\Sigma_2^p$, and $\mathrm{NP}\subseteq\mathrm{BPP}$ implies $\mathrm{PH}\subseteq\mathrm{BPP}$. For the hard direction, fix an NP verifier $V$ and the witness set $W^x=\{w\in\{0,1\}^m : V(x,w)=1\}$. Language compression for $\mathrm{pnK}$ gives $\mathrm{pnK}^{\mathrm{poly}(n)}(w\mid x)\le\log|W^x|+O(\log n)$ for every witness $w$. The proof then shows that a BPP algorithm for MINnKT collapses conditional $\mathrm{pnK}$ to conditional $\mathrm{pK}$ up to a small additive term, which makes some witness easy to sample given $x$; to control the simulation overhead it works with an auxiliary measure $\ell$-$\mathrm{nK}^t_\gamma$. The argument uses the algorithm's efficiency, so it does not yield a Karp reduction from an NP-complete problem.

## Depends on

- [Nondeterministic time-bounded Kolmogorov complexity CND^t = nK^t](nondeterministic-time-bounded-complexity.md)
- [Probabilistic nondeterministic time-bounded complexity pnK^t](probabilistic-nondeterministic-complexity-pnkt.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [Language compression and conditional coding for pnK^t](language-compression-and-coding-for-pnkt.md)

## Sources

- Jinqiao Hu, Zhenjian Lu and Igor C. Oliveira, "Hardness of Computing Nondeterministic Kolmogorov Complexity", *41st Computational Complexity Conference (CCC 2026)*, LIPIcs, 2026, [doi:10.4230/LIPIcs.CCC.2026.9](https://doi.org/10.4230/LIPIcs.CCC.2026.9) (Theorems 1, 2, 3, 9, 33 and 34, Section 1.3, Lemma 47).
