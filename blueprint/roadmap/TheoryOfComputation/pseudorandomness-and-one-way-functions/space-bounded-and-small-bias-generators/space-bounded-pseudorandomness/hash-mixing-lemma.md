# Nisan's hash mixing lemma

Let $X$ be a finite set and $\{h_i : X \to X\}$ a pairwise independent family with uniform seed $i$. For $A, B \subseteq X$ of densities $\alpha = |A|/|X|$ and $\beta = |B|/|X|$, the density $D_i = |\{x \in A : h_i(x) \in B\}|/|X|$ has mean $\alpha\beta$ and variance exactly $\alpha\beta(1-\beta)/|X|$. Hence $\mathbb{E}_i |D_i - \alpha\beta| \le \sqrt{\alpha\beta/|X|}$: a random member of the family mixes every rectangle $A \times B$ up to an error that vanishes as $|X|$ grows.

## Proof sketch

$|X| D_i$ counts the points of $A$ retained in $B$; each is retained with probability $\beta$ and pairs independently with probability $\beta^2$, giving the variance. Cauchy–Schwarz turns the variance into the mean absolute deviation bound.

## Depends on

- [k-wise independent hash families](../../../../ComputerScience/data-structures/hashing/word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- N. Nisan, "Pseudorandom Generators for Space-Bounded Computation", Combinatorica, 1992.
