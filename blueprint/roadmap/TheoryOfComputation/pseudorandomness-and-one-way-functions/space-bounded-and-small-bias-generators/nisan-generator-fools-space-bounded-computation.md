# Nisan's generator fools space-bounded computation

There is a constant $c$ such that, with block length $b = c\,s$ and a pairwise-independent family on $\{0,1\}^b$ of seed length $O(b)$, Nisan's generator with $k$ levels is an $(s, \varepsilon)$-pseudorandom generator for read-once branching programs of width $2^s$ reading $2^k$ blocks of $b$ bits, with $\varepsilon \le k \cdot 2^{-s}$. Its seed length is $O(s \cdot k)$; for space $s = O(\log R)$ and length $R$ this is $O(\log^2 R)$.

## Proof sketch

Induct on the level. Replacing the second half's independent start block by $h(x)$ changes the acceptance probability by the mixing error of a pairwise-independent hash on the transition matrices between the middle layers; the mixing lemma bounds it by $2^{O(s)} \cdot 2^{-b/2} \le 2^{-s}$ per level for $b = cs$, and the errors add over the $k$ levels.

## Depends on

- [Nisan's generator for read-once branching programs](nisan-generator.md)

## Proof depends on

- [Leftover hash lemma](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma.md)

## Sources

- N. Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica 12(4), 1992.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
