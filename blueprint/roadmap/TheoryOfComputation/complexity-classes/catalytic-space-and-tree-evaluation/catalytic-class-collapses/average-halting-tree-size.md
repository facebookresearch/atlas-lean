# Koucký–Mertz–Pyne–Sami: halting 0-trees have average size at most 2^s over catalytic contents

Let $M$ be a valid catalytic machine with free space $s$ and catalytic space $c$, where $\log n\le s\le c\le 2^s$, and let $x\in\{0,1\}^n$. Then

$$
\mathbb{E}_{\tau\in\{0,1\}^c}\bigl[|T(\mathrm{acc}_\tau)|\bigr]\le 2^{s}\qquad\text{and}\qquad \mathbb{E}_{\tau\in\{0,1\}^c}\bigl[|T(\mathrm{rej}_\tau)|\bigr]\le 2^{s}.
$$

Consequently, by Markov's inequality and a union bound, more than half of all $\tau$ have both halting trees of size at most $4\cdot 2^{s}$.

## Proof sketch

By disjointness of halting trees for distinct catalytic contents, the trees $T(\mathrm{acc}_\tau)$ for $\tau\in\{0,1\}^c$ are pairwise disjoint subsets of the set of all $2^{c+s}$ configurations, so their sizes sum to at most $2^{c+s}$ and their average is at most $2^s$; the same holds for rejecting trees. Markov's inequality applied to each family and a union bound give the last sentence.

## Depends on

- [Configuration graphs and halting 0-trees of a catalytic machine](configuration-graphs-and-halting-zero-trees.md)
- [Valid catalytic machines with nondeterministic or random choices](valid-catalytic-machines-with-choices.md)

## Proof depends on

- [Halting 0-trees of different catalytic contents are disjoint and cover all reachable configurations](halting-zero-trees-disjoint-and-covering.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
