# Goldwasser–Grossman–Mohanty–Woodruff: no pseudodeterministic low-memory turnstile algorithm finds a nonzero entry

In **Find-Support-Elem** a vector $v\in\mathbb{Z}^n$, initially $0$, is given by a turnstile stream of updates "increase $v_i$ by 1" or "decrease $v_j$ by 1", and the goal is to output an index $i$ with $v_i\neq 0$ in the final vector (promised nonzero). Randomized algorithms solve it in polylogarithmic space, but:

1. no pseudodeterministic streaming algorithm for Find-Support-Elem uses $\tilde o(n)$ memory;
2. every randomized algorithm for Find-Support-Elem using $o(s)$ space has an input stream $x$ on which its output $A(x)$, as a random variable, has entropy at least $\log\bigl(n/(s\log n)\bigr)$; in particular space $n^{1-\varepsilon}$ forces entropy $\Omega(\log n)$.

By contrast, finding a nonzero row of an $n\times d$ matrix given in a turnstile stream has randomized space complexity $\tilde\Theta(1)$, pseudodeterministic space complexity $\tilde\Theta(n)$ and deterministic space complexity $\tilde\Theta(nd)$.

## Proof sketch

A low-memory pseudodeterministic algorithm for Find-Support-Elem yields a pseudodeterministic one-way communication protocol of comparable cost for One-Way-Find-Duplicate, in which Alice and Bob each hold a subset of $[n]$ of size $3n/4$ and must output an element they share: the players encode their sets as turnstile updates whose final vector is supported on common elements, and Alice sends the memory state. The lower bound is then proved for pseudodeterministic one-way protocols, whose canonical answer depends only on the inputs, by a counting argument over Bob's possible sets. The nonzero-row upper bound multiplies the matrix by a random vector and deterministically finds a nonzero entry of the product.

## Depends on

- [Pseudodeterministic algorithms for search problems (Gat–Goldwasser)](pseudodeterministic-algorithm-for-search-problem.md)
- [Randomized streaming algorithm with $s$ bits of memory](../../../../ComputerScience/randomized-algorithms/frequency-moments-of-data-streams/streaming-algorithm.md)

## Sources

- Shafi Goldwasser, Ofer Grossman, Sidhanth Mohanty and David P. Woodruff, "Pseudo-Deterministic Streaming", ITCS (2020), arXiv:1911.11368.
