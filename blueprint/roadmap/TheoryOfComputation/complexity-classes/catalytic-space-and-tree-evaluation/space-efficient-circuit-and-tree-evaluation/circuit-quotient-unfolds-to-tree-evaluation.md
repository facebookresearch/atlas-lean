# Shalunov: a block quotient of a circuit unfolds into a Tree Evaluation instance

Let $C$ be a Boolean circuit of size $s$ with fan-in at most $2$ and $P$ a partition of its gates (or of a subdivision) into blocks of at most $b$ gates, with acyclic quotient of maximum in-degree $d$ and longest path $h$. Then evaluating $C$ on an input $x$ reduces to a Tree Evaluation instance of arity $d$, height $h$ and value size $b$ bits, in which each node value is the vector of the $b$ gate values of a block and each node function, mapping $d$ input vectors of $b$ bits to $b$ bits, is computable in space $O(b+\log s)$ from $C$ and $x$. Unfolding the quotient DAG into a tree duplicates blocks once per path but never changes the height, and the tree is never written down. Combined with the Cook–Mertz evaluation procedure, which uses space $O(h\log(db)+db)$ for such instances, this evaluates $C$ in space $O(h\log(db)+db)$.

## Proof sketch

Each block's gate values are determined by the values of its predecessor blocks and the input, so the quotient is a circuit over the alphabet $\{0,1\}^b$, and expanding a circuit into a formula by duplicating shared subcomputations gives a tree of the same height. The Cook–Mertz procedure only queries node functions and leaf values, which can be recomputed on demand by simulating a single block, and its space bound is stated in terms of height, arity and value size.

## Depends on

- [The Circuit Value Problem](../../../completeness-other-classes/circuit-value-problem/cvp-dec.md)

## Proof depends on

- [Shalunov's low-degree DAG partition lemma](shalunov-low-degree-dag-partition.md)

## Sources

- Yakov Shalunov, "Improved Bounds on the Space Complexity of Circuit Evaluation", CCC (2026), arXiv:2504.20950.
- James Cook and Ian Mertz, "Tree Evaluation Is in Space O(log n · log log n)", STOC (2024), ECCC TR23-174.
