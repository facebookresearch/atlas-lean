# A relativized world where MCSP is easy but search-MCSP is hard

Ren and Santhanam construct oracles relative to which MCSP is decidable in linear time, while no deterministic $N^c$-time machine outputs even a circuit of size $2^n/4n$ for every truth table of circuit complexity at most $4cn$. So a deterministic search-to-decision reduction for MCSP, even an approximate one, needs non-relativizing techniques.

Meta-computational problems relativize by giving the same oracles $\mathcal{O}$ both to the algorithms and to the circuits whose size is measured. Circuit size is the number of wires, oracle gates may have any fan-in, and $\mathrm{CC}^{\mathcal{O}}(x)$ is the minimum size of an $\mathcal{O}$-oracle circuit whose truth table is $x$. Then $\mathrm{MCSP}^{\mathcal{O}}[x, s] = 1$ if and only if $\mathrm{CC}^{\mathcal{O}}(x) \le s$, and for a size function $s(n)$ the problem $\mathrm{MCSP}^{\mathcal{O}}[s(n)]$ asks whether $\mathrm{CC}^{\mathcal{O}}(x) \le s(n)$ for a truth table $x$ of length $N = 2^n$. Search-$\mathrm{MCSP}^{\mathcal{O}}$ asks, given $x$, for an $\mathcal{O}$-oracle circuit of size $\mathrm{CC}^{\mathcal{O}}(x)$ computing $x$. A problem *requires time* $T(N)$ if every deterministic oracle machine running in time $T(N)$ fails on infinitely many inputs. Each item below holds relative to its own pair of oracles $\mathcal{O} = (O, \mathrm{itrMCSP})$, where the machines and circuits of the item may query both.

1. $\mathrm{MCSP}^{\mathcal{O}}$ is decidable in linear time, but search-$\mathrm{MCSP}^{\mathcal{O}}$ requires time $2^{\Omega(N/\log N)}$.
2. Let $c \ge 2$ be a constant. $\mathrm{MCSP}^{\mathcal{O}}$ is decidable in linear time, and for every deterministic oracle machine $M$ running in time $N^c$ there is a truth table $x$ of length $N = 2^n$ with $\mathrm{CC}^{\mathcal{O}}(x) \le 4cn$ such that $M$ on input $x$ does not output an $\mathcal{O}$-oracle circuit of size $2^n/4n$ that computes $x$.
3. Let $0 < \delta_1 < \delta_2 < 1$ be constants with $1/\delta_1 - 1/\delta_2 > 1$. $\mathrm{MCSP}^{\mathcal{O}}[2^{\delta_2 n}]$ is decidable in linear time, but $\mathrm{MCSP}^{\mathcal{O}}[2^{\delta_1 n}]$ requires time $2^{N^{\delta_1}}/N^{\omega(1)}$.
4. Let $0 < \delta_1 < \delta_2 < 1$ be constants. $\mathrm{MCSP}^{\mathcal{O}}[2^{\delta_1 n}]$ has a linear-time zero-error heuristic under the uniform distribution, but no deterministic oracle machine running in time $2^{N^{\delta_2}}/N^{\omega(1)}$ accepts at least one truth table of every large enough length $N$ while rejecting every truth table of length $N$ whose $\mathcal{O}$-oracle circuit complexity is at most $2^{\delta_2 n}$. So no property of positive density that is useful against $\mathcal{O}$-oracle circuits of size $2^{\delta_2 n}$ is computable in that time.

## Proof sketch

The oracle $\mathrm{itrMCSP}[k, x, s]$ answers MCSP for circuits that may call $O$ and $\mathrm{itrMCSP}$ with iteration number below $k$, so $\mathrm{MCSP}^{\mathcal{O}}[x, s] = \mathrm{itrMCSP}[2N, x, s]$ is computed by one query. To make search hard, the construction diagonalizes against each machine $M$: it fixes $O$ below length $N_i$, answers queries with threshold at least $N_i + 1$ as if the truth table were easy, then plants those tables and a hard table $x_{\mathrm{hard}}$ in unprobed positions of the length-$(N_i + 1)$ slice of $O$. Then $x_{\mathrm{hard}}$ has a circuit of size $N_i + 1$ that $M$ fails to find. Item 2 uses the same plan with a table of circuit complexity above $\tilde N/4\log \tilde N$ before planting. This contrasts with the relativizing randomized approximate search-to-decision reduction of Carmosino, Impagliazzo, Kabanets and Kolokolova.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Zero-error average-case devices for MCSP](../../../circuit-complexity/minimum-circuit-size-problem/zero-error-average-case-devices-for-mcsp.md)
- [Polynomial time with an oracle](../../../complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)
- [Oracle circuits and local circuit classes](../../../circuit-complexity/hardness-magnification/oracle-circuits-and-local-circuit-classes.md)

## Proof depends on

None.

## Sources

- Hanlin Ren and Rahul Santhanam, "A Relativization Perspective on Meta-Complexity", *STACS* 2022, LIPIcs 219, Article 54, DOI 10.4230/LIPIcs.STACS.2022.54 (abstract items 1 and 2 and Theorem 13, informal version, Section 2.1; proof overview in Section 3.1).
- Hanlin Ren and Rahul Santhanam, "A Relativization Perspective on Meta-Complexity", full version, ECCC TR21-089, 25 June 2021, <https://eccc.weizmann.ac.il/report/2021/089/> (Theorem 3.1, its three items proved in Sections 3.1, 3.2 and 3.3; Theorem 3.4, Section 3.1; the oracle model and Definitions 2.1 and 2.2 in Section 2).
