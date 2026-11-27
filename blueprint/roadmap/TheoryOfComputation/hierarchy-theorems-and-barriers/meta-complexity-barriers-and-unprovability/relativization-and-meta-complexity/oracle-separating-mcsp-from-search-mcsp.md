# A relativized world where MCSP is easy but search-MCSP is hard

Ren and Santhanam construct an oracle relative to which deciding MCSP takes deterministic polynomial time while no deterministic polynomial-time algorithm finds minimum circuits, even approximately. So a search-to-decision reduction for MCSP needs non-relativizing techniques.

Meta-computational problems relativize by giving the same oracle $A$ both to the algorithms and to the circuits whose size is measured: $\mathrm{MCSP}^A[x, s] = 1$ if and only if the truth table $x$ has an $A$-oracle circuit of size at most $s$. There is an oracle $A$ such that $\mathrm{MCSP}^A \in \mathsf{P}^A$, but search-$\mathrm{MCSP}^A$ (given a truth table, output a minimum-size $A$-oracle circuit for it) cannot be solved by deterministic polynomial-time machines with oracle $A$, even approximately. The same method gives relativized worlds where $\mathrm{MCSP}[2^{n/2}] \in \mathsf{P}$ while $\mathrm{MCSP}[2^{n/4}]$ is very hard, and where $\mathrm{MCSP}[2^{n/4}]$ has a polynomial-time errorless heuristic while $\mathrm{MCSP}[2^{n/2}]$ does not.

## Expansion

Adding an MCSP oracle changes the problem to $\mathrm{MCSP}^{\mathrm{MCSP}}$, so the oracle includes the iterated problem $\mathrm{itrMCSP}[k, x, s]$, the $k$-fold iterate of relativized MCSP, which makes circuit minimization easy in the limit. To make search hard, the construction diagonalizes against each machine $M$: it fixes the oracle below length $N$, answers queries with threshold at least $N$ as if the truth table were easy, then plants those tables and a hard table $x_{\mathrm{hard}}$ in unprobed positions of the length-$N$ slice. Then $x_{\mathrm{hard}}$ has a size-$N$ circuit that $M$ fails to find. This contrasts with the relativizing randomized approximate search-to-decision reduction of Carmosino, Impagliazzo, Kabanets and Kolokolova.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Zero-error average-case devices for MCSP](../../../circuit-complexity/minimum-circuit-size-problem/zero-error-average-case-devices-for-mcsp.md)

## Proof depends on

None.

## Sources

- Hanlin Ren and Rahul Santhanam, "A Relativization Perspective on Meta-Complexity", *STACS* 2022, LIPIcs 219, Article 54, DOI 10.4230/LIPIcs.STACS.2022.54 (abstract item 1 and items 1 to 3 of Theorem 13, Section 2.1; proof overview in Section 3.1; formal statements in the full version).
