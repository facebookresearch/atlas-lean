# Sparse synthesis at the square root of the cube

Let $n=2p$. For every $\varepsilon>0$ and all sufficiently large $p$:

- the indicator function of every set $S\subseteq\{0,1\}^n$ with $|S|\le 2^p$ has a De Morgan circuit with at most $(1+\varepsilon)2^p$ gates (the case $N=2^p$ of Lupanov's bound for functions with $N$ ones);
- for every set $D\subseteq\{0,1\}^n$ with $|D|\le 2^p$ and every $g:D\to\{0,1\}$, some De Morgan circuit with at most $(1+\varepsilon)2^p/p$ gates agrees with $g$ on $D$ (the case of Sholomov's bound $|D|/\log_2|D|$ for partial functions).

Both bounds are asymptotically optimal.

## Proof sketch

Both bounds are cases of the general estimate $C(f)\le(1+o(1))\,\log_2\binom{D}{N}\big/\log_2\log_2\binom{D}{N}+O(n)$ for a partial function defined on $D$ points and equal to $1$ on $N$ of them, proved by local coding combined with linear hashing of the domain into a smaller cube. For the indicator take $D=2^{2p}$, $N=|S|\le 2^p$, where $\log_2\binom{2^{2p}}{2^p}=(1+o(1))\,p\,2^p$; for partial functions $\log_2\binom{D}{N}\le D\le 2^p$. In both cases the additive $O(n)=O(p)$ term is absorbed.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [All minterms in linear size](../circuit-synthesis-upper-bounds/all-minterms-in-linear-size.md)

## Sources

- O. B. Lupanov, "On an Approach to the Synthesis of Control Systems: the Principle of Local Coding", Problemy Kibernetiki 14, 31–110, 1965.
- L. A. Sholomov, "On the Realization of Incompletely Defined Boolean Functions by Circuits of Functional Elements", Problemy Kibernetiki, 1969.
- A. V. Chashkin, "On Computing Partial Boolean Functions", Matematicheskie Voprosy Kibernetiki 22, 152–222, 2024 (inequality (1.1)).
