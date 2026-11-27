# A relativized world without natural proofs and without one-way functions

For each $\delta \in (0,1)$, Ren and Santhanam give an oracle relative to which no natural property of size $2^{o(N^\delta)}$ and density $2^{-o(N^\delta)}$ is useful against circuits of size $2^{\delta n}$, yet auxiliary-input one-way functions do not exist. So basing one-way functions on the non-existence of natural proofs requires non-relativizing techniques.

Let $N = 2^n$ be the length of a truth table of an $n$-variable function. In each item below, all algorithms, circuits and samplers may query the oracles of the world, and auxiliary-input one-way functions do not exist in that world.

1. For every constant $\delta \in (0,1)$ there is a relativized world with no $\mathsf{SIZE}[2^{o(N^\delta)}]$-natural property useful against $\mathsf{SIZE}[2^{\delta n}]$ with density $2^{-o(N^\delta)}$: no family of circuits of size $2^{o(N^\delta)}$ accepts at least a $2^{-o(N^\delta)}$ fraction of the truth tables of length $N$ while rejecting every truth table of circuit complexity at most $2^{\delta n}$. In particular there is no $\mathsf{P/poly}$-natural property of density $1/\mathrm{poly}(N)$ useful against $\mathsf{SIZE}[2^{\delta n}]$.
2. There is a relativized world with a polynomial-time samplable sequence of distributions $D_n$ on MCSP instances of length $\mathrm{poly}(n)$ such that no circuit of size $2^{o(n)}$ decides MCSP with error probability below $0.01$ over $D_n$. The instances come from a language $L_{\mathrm{hard}} \in \mathsf{NP}$ that circuits of size $2^{0.1n}$ cannot decide on a $0.99$ fraction of inputs of length $n$, mapped in polynomial time to truth tables $h_y$ such that $h_y$ has circuits of size $O(n)$ if $y \in L_{\mathrm{hard}}$, while for $y \notin L_{\mathrm{hard}}$ no circuit of size $n^{c/200}$ agrees with $h_y$ on a $1/2 + n^{-c/200}$ fraction of inputs, where $c$ is a large constant of the construction.
3. For every large enough constant $c$ there is a relativized world in which, under some polynomial-time samplable distribution, $\mathrm{Gap}_{\sigma,\tau}\mathrm{MINKT}$ with $\sigma(s) = s^c$ and $\tau(t) = t^c$ cannot be $0.99$-approximated by circuits of size $2^{o(n)}$. Its yes-instances are the triples $(x, 1^s, 1^t)$ with $K^t(x) \le s$ and its no-instances those with $K^{t^c}(x) > s^c$.

## Context

The non-existence of natural proofs is equivalent to the zero-error average-case hardness of MCSP, and Santhanam showed with a relativizing proof that, under a universality conjecture about optimal hitting sets, it implies one-way functions; the first world shows that the universality conjecture fails relative to an oracle. Because one-way functions are equivalent to two-sided-error average-case hardness of MINKT under the uniform distribution, and because the absence of auxiliary-input one-way functions forces $\mathsf{CZK} = \mathsf{BPP}$, the third world shows that extending Hirahara's worst-case to average-case reduction to two-sided error over the uniform distribution, or proving $\mathrm{GapMINKT} \in \mathsf{CZK}$, needs non-relativizing techniques. All three worlds follow one template: a base oracle, a $\mathsf{PSPACE}$-complete oracle, Kolmogorov-random functions $f_n$ and a trapdoor oracle that inverts $f_n$ only for callers holding a preimage.

## Depends on

- [Natural property](../../natural-proofs-barrier/natural-property.md)
- [Auxiliary-input one-way functions](../../../pseudorandomness-and-one-way-functions/worst-case-characterizations-of-one-way-functions/auxiliary-input-one-way-functions.md)
- [The time-bounded Kolmogorov complexity problem MINKT](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/the-minkt-problem.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

None.

## Sources

- Hanlin Ren and Rahul Santhanam, "A Relativization Perspective on Meta-Complexity", *STACS* 2022, LIPIcs 219, Article 54, DOI 10.4230/LIPIcs.STACS.2022.54 (abstract item 4 and Theorems 16, 17 and 18, informal versions, Section 2.3; proof overview in Section 3.3).
- Hanlin Ren and Rahul Santhanam, "A Relativization Perspective on Meta-Complexity", full version, ECCC TR21-089, 25 June 2021, <https://eccc.weizmann.ac.il/report/2021/089/> (Theorem 5.1 and the construction of Section 5.1; item 1 as Theorem 5.5, Section 5.2; item 2 from Section 5.3 with Lemmas 5.8 and 5.9; item 3 as Theorem 5.10, Section 5.4; Definition 2.7 of natural properties and Definition 2.9 of auxiliary-input one-way functions).
