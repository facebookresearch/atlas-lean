# Checking each listed vertex pair against its bit

Let $n$ be a natural number and $b$ a
list of bits with one bit per vertex pair, that is, with as many entries as the list of pairs
$(i, j)$ with $i < j < n$. Then for every Boolean predicate $P$ on a pair of natural numbers and
a bit, $P$ holds on every entry of the pair list zipped with $b$ (the $t$-th pair together with
the $t$-th bit of $b$) if and only if, for all natural numbers $i < j < n$, $P$ holds on the
pair $(i, j)$ together with the adjacency bit of $\{i, j\}$ in $b$.
