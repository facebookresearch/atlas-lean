# Context unification is in PSPACE


For a fixed finite signature, satisfiability of context equations is decidable in polynomial space, by recompression on terms.

Let $\Sigma$ be a fixed finite signature containing a constant, with maximal arity $k \ge 1$, and measure a [context equation](context-unification.md) $u = v$ over $\Sigma$ by its size $n$, the number of symbol occurrences in $u$ and $v$. There is a nondeterministic algorithm that

1. never accepts an unsolvable equation, and
2. for a solvable equation whose size-minimal solution has size $N$, accepts for suitable nondeterministic choices after $O(\log(N + 2))$ phases, while storing equations with $O(nk)$ symbols and using $O(n^2 k^2)$ additional bits.

Consequently context unification over $\Sigma$ is in $\mathrm{PSPACE}$. The bounds are polynomial in $n$ and $k$. This is not a completeness result: the cited sources record NP-hardness, inherited from word equations, as the lower bound.


## Depends on

- [Context unification](context-unification.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Savitch's theorem: NPSPACE = PSPACE](../../../complexity-classes/savitch.md)

## Expansion

The algorithm lifts recompression from words to trees. Pair compression and $a$-maximal chain compression act on chains of unary symbols as pair and block compression act on words, and leaf compression lets a symbol $f$ of arity $m$ absorb a constant child in a fixed argument position, giving a fresh symbol of arity $m - 1$. Each compression is applied to non-crossing occurrences and made possible for crossing ones by popping symbols out of the values of variables and context variables. On a ground tree with at least two nodes, one round of these compressions, for a suitable partition of the unary letters, yields a tree of size less than three quarters of the original, so the size-minimal solution shrinks by a constant factor per phase. Each context variable owns at most $k - 1$ first-order variables, which keeps the equation at $O(nk)$ symbols, and the popped chain lengths are at most exponential by the exponent-of-periodicity bound for context equations, used only for unary letters; this gives $O(n^2 k^2)$ bits. Savitch's theorem turns the nondeterministic polynomial-space procedure into a deterministic one.

This page becomes ready once the following are pages of their own: the shrinking of trees by one round of compressions (Jeż, Theorem 1), the exponent-of-periodicity bound for context equations (Lemma 5), the simpler-equivalent lemma (Lemma 7), and the soundness and phase invariants of the algorithm (Lemmas 15–18).

## Sources

- Artur Jeż, "Context Unification is in PSPACE", ICALP 2014, LNCS 8573, 244–255 (2014), https://doi.org/10.1007/978-3-662-43951-7_21; read as arXiv:1310.4367v2, https://arxiv.org/abs/1310.4367v2, Theorem 2 and Corollary 1 (Section 6, "Main algorithm"), Lemma 15 for the split between symbols and bits, Theorem 1 (Section 2), Lemmas 5 and 7 (Section 3) and Lemmas 16–18
- Artur Jeż, "Recompression: New Approach to Word Equations and Context Unification (Invited Talk)", STACS 2017, LIPIcs 66, Article 2 (2017), https://doi.org/10.4230/LIPIcs.STACS.2017.2, which records the PSPACE upper bound and the NP lower bound
