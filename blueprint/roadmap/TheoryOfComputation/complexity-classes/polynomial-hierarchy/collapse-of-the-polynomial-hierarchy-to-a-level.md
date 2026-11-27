# Collapse of the polynomial hierarchy to a level

**Theorem.** For every $i \ge 1$, if $\Sigma^p_i = \Pi^p_i$ then $\mathsf{PH} = \Sigma^p_i$: the polynomial hierarchy collapses to its $i$-th level.

The case $\mathsf{P} = \mathsf{NP}$, which gives $\mathsf{PH} = \mathsf{P}$, is proved by induction on the level; the proof for $\Sigma^p_i = \Pi^p_i$ is similar: an existential or universal
quantifier in front of a $\Sigma^p_i$ predicate is absorbed into a $\Pi^p_i = \Sigma^p_i$ predicate, so $\Sigma^p_{j} = \Sigma^p_i$ for all $j \ge i$.

## Depends on

- [The polynomial hierarchy](../time-and-space-complexity-classes/ph.md)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, <https://theory.cs.princeton.edu/complexity/>: Section 5.2 and Theorem 5.6, part 1, with the proof of part 2 and the remark that part 1 is similar.
