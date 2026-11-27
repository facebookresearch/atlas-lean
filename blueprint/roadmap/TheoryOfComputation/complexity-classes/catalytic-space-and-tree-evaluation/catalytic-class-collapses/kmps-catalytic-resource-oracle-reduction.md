# Koucký–Mertz–Pyne–Sami: catalytic space with extra resources reduces to plain space with one oracle query

Let $\mathcal{B}\in\{\mathrm{N},\mathrm{coN},\mathrm{BP},\mathrm{Pr}\}$. For all $s=s(n)$ and $c=c(n)$ with $\log n\le s\le c\le 2^{s}$,

$$
\mathsf{C}\mathcal{B}\mathsf{SPACE}[s,c]\subseteq \mathsf{CSPACE}[O(s),O(c)]^{\mathcal{B}\mathsf{SPACE}[O(s)]},
$$

where the deterministic catalytic oracle machine makes a single query, of length $2^{O(s)}$, whose answer is the output; for $\mathcal{B}\in\{\mathrm{BP},\mathrm{Pr}\}$ the oracle is the corresponding promise class. Equivalently, there is a $\mathsf{CSPACE}[O(s),O(c)]$-computable reduction from $\mathsf{C}\mathcal{B}\mathsf{SPACE}[s,c]$ to $\mathcal{B}\mathsf{SPACE}[O(s)]$ followed by a postprocessing phase that restores the catalytic tape regardless of the oracle answer.

## Proof sketch

Pad the catalytic tape with $O(c)$ extra bits split into $B$-bit blocks and apply compute-or-compress repeatedly, each time to the current content and a fresh block. Either some call is in the compute case, and the small graph $(G,r,t)$ is a faithful copy of the reachable configuration graph, on which the original $\mathcal{B}$-acceptance condition (reachability, its complement, or acceptance probability of the induced random walk) is a $\mathcal{B}\mathsf{SPACE}[O(s)]$ question on an input of length $2^{O(s)}$; or after $O(c/s)$ compress steps $c$ bits are free, and one brute-forces a fresh content $\tau'$ whose halting trees are small, which exists by the averaging lemma, and asks the same question for $\tau'$. Finally all compressions are undone in reverse order with $\mathrm{COUNTSTEPSBACK}$.

## Depends on

- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)

## Proof depends on

- [Koucký–Mertz–Pyne–Sami compute-or-compress lemma for catalytic configuration graphs](kmps-compute-or-compress-lemma.md)
- [Koucký–Mertz–Pyne–Sami: halting 0-trees have average size at most 2^s over catalytic contents](average-halting-tree-size.md)
- [Halting 0-trees of different catalytic contents are disjoint and cover all reachable configurations](halting-zero-trees-disjoint-and-covering.md)

## Sources

- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
