# Feasible instances of ROOTED TREE STORAGE ASSIGNMENT

An instance $(N, (X_1, \dots, X_n), K)$ of ROOTED TREE STORAGE ASSIGNMENT, with $X = \{0, \dots, N - 1\}$, is feasible when there are sets $X_1', \dots, X_n' \subseteq X$ such that

- each $X_i'$ contains every element of the list $X_i$ that lies in $X$ (listed entries $\ge N$ are not tested);
- at most $K$ elements are added in total: $\sum_i |\{x \in X_i' : x \text{ is not listed in } X_i\}| \le K$; and
- there is a tree $T$ on $X$ with a root $r$ in which every $X_i'$ is the vertex set of a simple path $p$ from $u$ to $v$ running away from the root: $\operatorname{dist}(r, v) = \operatorname{dist}(r, u) + \operatorname{length}(p)$.

On raw input this test ignores out-of-range entries: with $N = 1$, the single list $X_1 = [1]$ and $K = 1$, the set $X_1' = \{0\}$, the one-vertex tree and its path of length $0$ satisfy it. The separate [well-formedness](rooted-tree-storage-assignment-well-formed.md) predicate rejects lists with entries outside $X$, and for a well-formed instance the conditions read $X_i' \supseteq X_i$.
