# Doubly exponential bound on length-minimal solutions

A word equation of size $n$ with $n_v$ occurrences of variables that has a nonerasing solution has a length-minimal solution of length at most $2^{q(n)\, n_v^{c\, n_v}}$ for a fixed polynomial $q$ and constant $c$.

There are a polynomial $q$ and a constant $c$ such that every word equation $U = V$ of size $n = |U| + |V|$ with $n_v$ occurrences of variables that has a nonerasing solution has a length-minimal solution $\sigma$ with

$$
N = |\sigma(U)| \le 2^{q(n) \cdot n_v^{c\, n_v}} ,
$$

where $0^0 = 1$, so that for an equation without variables the bound reads $2^{q(n)}$. Since $n_v \le n$, also $N \le 2^{2^{O(n \log n)}}$ for $n \ge 2$. Whether every satisfiable equation has a solution of singly exponential length is not settled by this bound.

## Depends on

- [Length-minimal solution of a word equation](length-minimal-solution.md)

## Proof depends on

- [Soundness and completeness of recompression](../recompression/recompression-is-sound-and-complete.md)
- [Size of minimal natural solutions of linear Diophantine systems](minimal-solutions-of-linear-diophantine-systems.md)

## Expansion

The bound was first proved by W. Plandowski (STOC 1999). The recompression proof compares two counts of phases. For appropriate choices, an accepting run of the recompression algorithm has at most $c\, n_v^{c\, n_v} \log n$ phases. In the other direction (Jeż, Lemma 40), every accepting run has $\Omega(\log N / p(n))$ phases for a polynomial $p$, whatever the choices. Each phase has one block-compression subphase and two pair-compression subphases. One pair-compression subphase shortens a length-minimal solution by a factor of at most $2$. One block-compression subphase, run in its improved form, shortens it by a factor of at most $c\, n\, e^{2 n_v / e}$: among the solutions similar to a given one, those obtained from solutions of its coherent linear Diophantine system, a length-minimal one has all block lengths bounded through the minimal solutions of that system. Comparing the two counts gives $c' \log N / p(n) \le c\, n_v^{c\, n_v} \log n$.

This page becomes ready once the following are pages of their own: the improved block compression with its coherent Diophantine systems (Jeż, Lemmas 15–20), the bound on block lengths of length-minimal solutions among similar solutions (Jeż, Lemmas 37–38), and the lower bound on the number of phases (Jeż, Lemma 40).

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Corollary 1 and its proof (Section 8, "Double exponential bound on minimal solutions"), with Lemma 40 (lower bound on the number of phases) and Lemma 9 (upper bound on the number of phases)
