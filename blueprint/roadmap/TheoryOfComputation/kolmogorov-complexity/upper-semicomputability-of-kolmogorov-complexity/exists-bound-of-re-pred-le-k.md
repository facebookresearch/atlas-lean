# Chaitin's incompleteness theorem

Let $K$ denote Kolmogorov complexity, and let $S$ be a
recursively enumerable (recognizable) set of pairs $(x, n)$ of a binary string $x$ and a natural
number $n$ such that $n \le K(x)$ for every $(x, n) \in S$. Then there is a natural number $B$
with $n \le B$ for every $(x, n) \in S$.

This is the abstract form of the theorem: think of $S$ as the statements $K(x) \ge n$ that a sound
formal system proves. The proof searches $S$ for a pair with a large bound $n$ and applies
optimality of the universal description method (Berry's paradox).
