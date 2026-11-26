# Cook–Mertz: Tree Evaluation in space O(h log k / log h), i.e. O(log^2 n / log log n)

Recall that an instance of Tree Evaluation $\mathrm{TreeEval}_{k,h}$ (binary version) is a complete binary tree of height $h$ whose leaves carry values in $[k]$ and whose internal nodes carry explicit function tables $f_v:[k]\times[k]\to[k]$; the task is to output the value of the root, evaluated bottom-up. The input length is $n=2^{\Theta(h)}\cdot\mathrm{poly}(k)$, so $\log n=\Theta(h+\log k)$, and the depth-first (pebbling) algorithm uses space $\Theta(h\log k)$.

Cook and Mertz showed that for all $k$ and $h$, $\mathrm{TreeEval}_{k,h}$ can be computed in deterministic space

$$
O\Bigl(\frac{h\log k}{\log h}\Bigr),
$$

which is at most $O(\log^2 n/\log\log n)$. This refutes the intuition, behind the pebbling lower bound $\Omega(h\log k)$ for thrifty or read-once models, that each of the $h$ levels must hold its own $\log k$-bit value, and it predates the later improvement to $O(\log n\cdot\log\log n)$.

## Proof sketch

The algorithm is a uniform, space-bounded version of the catalytic register programs: registers holding encoded node values are shared across levels, each level adding its contribution transparently onto arbitrary contents and later cancelling it. An encoding of $[k]$-values that lets one register block serve about $\log h$ consecutive levels reduces the total register space by a $\log h$ factor relative to the $h\log k$ stack of the pebbling algorithm.

## Depends on

- [Cook–Mertz 2020: catalytic branching programs beating the pebbling algorithm for Tree Evaluation](cook-mertz-catalytic-branching-programs-treeeval.md)

## Proof depends on

- [Cook–Mertz 2020: catalytic branching programs beating the pebbling algorithm for Tree Evaluation](cook-mertz-catalytic-branching-programs-treeeval.md)

## Sources

- James Cook and Ian Mertz, "Encodings and the Tree Evaluation Problem", ECCC TR21-054 (2021).
- James Cook and Ian Mertz, "Catalytic Approaches to the Tree Evaluation Problem", STOC (2020), ECCC TR20-056.
- James Cook and Ian Mertz, "Tree Evaluation Is in Space O(log n · log log n)", STOC (2024), ECCC TR23-174.
