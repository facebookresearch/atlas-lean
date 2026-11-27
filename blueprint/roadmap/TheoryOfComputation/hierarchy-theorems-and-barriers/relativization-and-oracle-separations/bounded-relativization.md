# Bounded relativization

A complexity statement is $\mathcal{C}$-relativizing if it holds relative to every oracle in the class $\mathcal{C}$. Every relativizing statement is $\mathcal{C}$-relativizing for every $\mathcal{C}$, yet non-relativizing results such as $\mathsf{IP}=\mathsf{PSPACE}$ are $\mathsf{PSPACE}$-relativizing.

Let $\mathcal{C}$ be a complexity class. A complexity-theoretic statement is $\mathcal{C}$-relativizing if it is true relative to every oracle $O\in\mathcal{C}$. Conventions: when a space-bounded machine is relativized, its query tape counts toward the space bound, so a $\mathsf{PSPACE}^O$ machine queries $O$ only on polynomially long strings and $\mathsf{PSPACE}^{\mathsf{PSPACE}}=\mathsf{PSPACE}$; $\mathsf{EXP}^O$ and $\mathsf{NEXP}^O$ machines may ask exponentially long queries, and $\mathsf{EXP}^{O[\mathrm{poly}]}$, $\mathsf{NEXP}^{O[\mathrm{poly}]}$ denote the versions restricted to polynomial-length queries. $\mathsf{EXPH}$ is the exponential-time hierarchy: languages decided by an exponential-time alternating machine with a constant number of alternations.

Basic facts:

1. For every oracle $O\in\mathsf{PSPACE}$, $\mathsf{IP}^O=\mathsf{PSPACE}^O$.
2. For every $O\in\mathsf{NEXP}\cap\mathsf{coNEXP}$, $\mathsf{MIP}^O=\mathsf{NEXP}^{O[\mathrm{poly}]}$.
3. For every computable $O$, $(\mathsf{MIP}^*)^O=\mathsf{RE}^O$.

An oracle $O\in\mathsf{EXPH}$ relative to which a statement fails is a bounded-relativization barrier: any $\mathsf{PSPACE}$-relativizing proof of the statement would also prove $\mathsf{PSPACE}\ne\mathsf{EXPH}$, and hence $\mathsf{L}\ne\mathsf{NP}$.

## Expansion

For item 1, the inclusion $\mathsf{IP}^O\subseteq\mathsf{PSPACE}^O$ relativizes, and for $O\in\mathsf{PSPACE}$ we have $\mathsf{PSPACE}^O=\mathsf{PSPACE}=\mathsf{IP}\subseteq\mathsf{IP}^O$. Items 2 and 3 follow the same pattern from $\mathsf{MIP}=\mathsf{NEXP}$ and $\mathsf{MIP}^*=\mathsf{RE}$. Results proved by combining interactive proofs with relativizing techniques inherit the same bounded relativization once each use of an interactive-proof theorem is replaced by its bounded-relativizing form. For the barrier, if $O\in\mathsf{EXPH}$ refutes the statement and $\mathsf{PSPACE}=\mathsf{EXPH}$, then $O\in\mathsf{PSPACE}$ and the $\mathsf{PSPACE}$-relativizing proof would hold relative to $O$.

## Depends on

- [Baker-Gill-Solovay: oracles separate and collapse P vs NP](baker-gill-solovay.md)
- [The class IP](../../complexity-classes/time-and-space-complexity-classes/ip.md)

## Proof depends on

- [IP = PSPACE (Shamir)](../../randomized-and-quantum-complexity/ip-eq-pspace.md)
- [MIP* = RE (Ji, Natarajan, Vidick, Wright, Yuen)](../../randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/mip-star-equals-re.md)

## Sources

- Shuichi Hirahara, Zhenjian Lu and Hanlin Ren, "Bounded Relativization", *38th Computational Complexity Conference (CCC 2023)*, LIPIcs, 2023, https://doi.org/10.4230/LIPIcs.CCC.2023.6 (Section 1.1, Proposition 1, Remark 2, Proposition 3, Definition 20).
