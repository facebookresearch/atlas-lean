# Nisan's generator for read-once branching programs

Let $\mathcal{H}$ be a pairwise-independent family of functions $h : X \to X$ on $X = \{0,1\}^b$. *Nisan's generator* with $k$ levels maps a seed $(x, h_1, \dots, h_k) \in X \times \mathcal{H}^k$ to $2^k$ blocks of $X$ defined recursively by $G_0(x) = x$ and

$$G_{j}(x; h_1, \dots, h_j) = G_{j-1}(x; h_2, \dots, h_j) \,\|\, G_{j-1}(h_1(x); h_2, \dots, h_j).$$

Equivalently, the block with binary index $\beta_1 \cdots \beta_k$ equals $h_k^{\beta_k}(\cdots h_2^{\beta_2}(h_1^{\beta_1}(x)))$. The seed has length $b + k \cdot \log_2|\mathcal{H}|$ and the output $b\,2^k$ bits.

## Depends on

- [Read-once branching program and space-bounded pseudorandom generator](read-once-branching-programs-and-space-bounded-prgs.md)
- [Universal hash family](../../../ComputerScience/data-structures/hashing/universal-hashing/is-universal.md)

## Sources

- N. Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica 12(4), 1992.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
