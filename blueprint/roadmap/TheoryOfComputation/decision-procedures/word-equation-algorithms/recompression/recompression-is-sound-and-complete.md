# Soundness and completeness of recompression


The recompression algorithm never accepts an unsatisfiable word equation, and an equation with a nonerasing solution is accepted by some run with $O(\log(N + 2))$ phases, where $N$ is the length of a length-minimal solution, storing equations of linear length.

Let $U = V$ be any word equation of size $n$ with $n_v$ occurrences of variables, and run the [recompression algorithm](recompression.md) on it, with block compression in its basic form, which writes popped blocks $a^\ell$ with $\ell$ in binary.

1. (Soundness) If some run accepts $U = V$, then $U = V$ has a solution, possibly erasing; so no run accepts an unsatisfiable equation.

Suppose moreover that $U = V$ has a nonerasing solution, and let $N \ge 0$ be the length of its length-minimal solutions ($N = 0$ when no variable occurs and both sides are empty).

2. (Completeness) For appropriate nondeterministic choices the run accepts after $O(\log(N + 2))$ phases, each taking time polynomial in $n$.
3. (Space) For appropriate nondeterministic choices, every stored equation has $O(n)$ symbols and the computation uses $O(n^2)$ bits of space.
4. (Phase count) For appropriate nondeterministic choices, the run accepts after $O(\log n + n_v^{c\, n_v})$ phases, for a constant $c$.

The choices in items 2–4 are made according to a length-minimal solution; items 2 and 4 are obtained by two different counting arguments. Rejecting every run that exceeds a space bound $C n^2$ or a step counter $2^{C n^2}$, for a suitable constant $C$, makes every run halt and still accepts every equation with a nonerasing solution, because a shortest accepting computation within the space bound repeats no configuration; both cutoffs are computable from the input. To decide satisfiability with possibly erasing solutions, first guess the set of variables with empty value and delete their occurrences; the input has a solution exactly when some such deletion has a nonerasing solution, so items 1–3 apply to the resulting equations.


## Depends on

- [Recompression algorithm for word equations](recompression.md)
- [Length-minimal solution of a word equation](../minimal-solutions/length-minimal-solution.md)

## Proof depends on

- [Recompression operations are sound](recompression-operations-are-sound.md)
- [Exponential bound on the exponent of periodicity](../minimal-solutions/exponential-bound-on-exponent-of-periodicity.md)

## Expansion

Soundness holds because every step is an instance of the sound operations. Completeness: guessing according to a fixed length-minimal solution, popping keeps the solution word unchanged and makes every pair of $\Gamma_\ell \Gamma_r$ noncrossing, so pair compression implements the compression of all these pairs in the solution word; cutting prefixes and suffixes does the same for blocks. The phase count of item 2 comes from Jeż's Claim 1: split the solution word into consecutive three-letter segments; a letter equal to a neighbour is compressed by block compression, and otherwise, for a uniformly random partition, a segment $abc$ has $ab \in \Gamma_\ell \Gamma_r$ or $bc \in \Gamma_\ell \Gamma_r$ with probability $1/2$; so some partition compresses at least $\lfloor |\sigma(U)| / 6 \rfloor$ letters, and the solution word shrinks by a constant factor per phase. The same argument applied to the explicit words of the equation, together with the fact that a phase introduces at most $6 n_v$ letters, keeps the stored equation of length at most $79 n$, and once its length is $O(n_v)$ the bounded number of such equations gives item 4. For item 3, individual letters take $O(\log n)$ bits; a popped block $a^\ell$ of a length-minimal solution has $\ell \le 2^{cn}$ by the bound on the exponent of periodicity, so it takes $O(n)$ bits, and at most $2 n_v$ such blocks are stored at a time.

This page becomes ready once the completeness lemmas for popping, pair compression, cutting of prefixes and suffixes and block compression (Jeż, Lemmas 5–8) and Claim 1 with the counting argument of Lemma 9 are pages of their own.

## Sources

- Artur Jeż, "Recompression: a simple and powerful technique for word equations", arXiv:1203.3705v3 (2014), https://arxiv.org/abs/1203.3705v3; published in Journal of the ACM 63(1), Article 4 (2016), https://doi.org/10.1145/2743014; conference version STACS 2013, LIPIcs 20, 233–244, https://doi.org/10.4230/LIPIcs.STACS.2013.233, Theorem 1 and Lemmas 9–11 with Claim 1 (Section 3), Lemmas 5–8 (Section 2) for completeness of the subprocedures, and Lemma 1 for the block lengths
