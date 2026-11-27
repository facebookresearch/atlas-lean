# Cook–Mertz: Tree Evaluation in space O(h log k / log h + h), i.e. O(log^2 n / log log n)

Recall that an instance of Tree Evaluation $\mathrm{TreeEval}_{k,h}$ (binary version) is a complete binary tree of height $h$ whose leaves carry values in $[k]$ and whose internal nodes carry explicit function tables $f_v:[k]\times[k]\to[k]$; the task is to output the value of the root, evaluated bottom-up. The input length is $n=2^{\Theta(h)}\cdot\mathrm{poly}(k)$, so $\log n=\Theta(h+\log k)$, and the depth-first (pebbling) algorithm uses space $\Theta(h\log k)$.

Cook and Mertz showed that for all $k$ and $h$, $\mathrm{TreeEval}_{k,h}$ can be computed in deterministic space

$$
O\Bigl(\frac{h\log k}{\log h} + h\Bigr),
$$

equivalently by branching programs of size $k^{O(h/\log h)}$ if $k\ge h$ and $2^{O(h)}$ if $k\le h$. In terms of the input length the space is $O(\log^2 n/\log\log n)$ and the branching-program size is $2^{O(\log^2 n/\log\log n)}$. This refutes the intuition, behind the pebbling lower bound $\Omega(h\log k)$ for thrifty or read-once models, that each of the $h$ levels must hold its own $\log k$-bit value, and it predates the later improvement to $O(\log n\cdot\log\log n)$.

## Proof sketch

The algorithm is a uniform, space-bounded version of the catalytic register programs: registers holding encoded node values are shared across levels, each level adding its contribution transparently onto arbitrary contents and later cancelling it. Node values are stored in the $d$-hot encoding: a value $x\in[k]$ is written as $d$ digits in a base $b$ with $b^d\ge k$, and each digit is one-hot encoded in $\{0,1\}^b$, which interpolates between the one-hot and binary encodings of the 2020 programs. Choosing $b$ and $d$ as functions of $h$ and $k$ gives the stated size and space bounds (Cook–Mertz 2021, §§3.1–3.2).

## Proof depends on

- [Cook–Mertz 2020: catalytic branching programs beating the pebbling algorithm for Tree Evaluation](cook-mertz-catalytic-branching-programs-treeeval.md)

## Sources

- James Cook and Ian Mertz, "Encodings and the Tree Evaluation Problem", ECCC TR21-054 (2021), Theorem 1, §§3.1–3.2.
- James Cook and Ian Mertz, "Catalytic Approaches to the Tree Evaluation Problem", STOC (2020), ECCC TR20-056.
- James Cook and Ian Mertz, "Tree Evaluation Is in Space O(log n · log log n)", STOC (2024), doi:10.1145/3618260.3649664; ECCC TR23-174 (its introduction records the earlier $O(h\log k/\log h)$, i.e. $O(\log^2 n/\log\log n)$, space bound).
