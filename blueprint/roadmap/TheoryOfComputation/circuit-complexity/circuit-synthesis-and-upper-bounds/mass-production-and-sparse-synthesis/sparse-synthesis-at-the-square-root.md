# Sparse synthesis at the square root of the cube

Let $n=2p$. For every $\varepsilon>0$ and all sufficiently large $p$:

- the indicator function of every set $S\subseteq\{0,1\}^n$ with $|S|\le 2^p$ has a De Morgan circuit with at most $(1+\varepsilon)2^p$ gates (the case $N=2^p$ of Lupanov's bound for functions with $N$ ones);
- for every set $D\subseteq\{0,1\}^n$ with $|D|\le 2^p$ and every $g:D\to\{0,1\}$, some De Morgan circuit with at most $(1+\varepsilon)2^p/p$ gates agrees with $g$ on $D$ (the case of Sholomov's bound $|D|/\log_2|D|$ for partial functions).

Both bounds are asymptotically optimal.

## Proof sketch

For the indicator, split inputs into two halves and use a perfect-hash style decomposition so that each element of $S$ is recognized by one conjunction of two shared half-minterms. For partial functions, apply Lupanov-type local coding to the $2^p$ defined points, which behave like a full truth table on $p$ variables.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [All minterms in linear size](../circuit-synthesis-upper-bounds/all-minterms-in-linear-size.md)

## Sources

- O. B. Lupanov, "On an Approach to the Synthesis of Control Systems: the Principle of Local Coding", Problemy Kibernetiki, 1965.
- L. A. Sholomov, "On the Realization of Incompletely Defined Boolean Functions by Circuits of Functional Elements", Problemy Kibernetiki, 1969.
- A. V. Chashkin, "On Computing Partial Boolean Functions", Matematicheskie Voprosy Kibernetiki, 2024.
