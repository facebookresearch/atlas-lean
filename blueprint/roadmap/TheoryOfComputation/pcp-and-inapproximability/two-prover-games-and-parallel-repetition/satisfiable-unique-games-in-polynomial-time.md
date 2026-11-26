# Satisfiable unique games are decidable in polynomial time

Fix a label set $[L]$. Given a unique game on a graph $(V, E)$ with bijections $\pi_e : [L] \to [L]$, one can decide in polynomial time whether it is fully satisfiable, and find a satisfying labelling when one exists. On the word-RAM the label-propagation algorithm runs in $O(L \cdot (|V| + |E|))$ steps. Consequently the gap problem $\mathrm{GapUG}(1, s)$ is in $\mathrm{PromiseP}$ for every $s < 1$, so the Unique Games Conjecture necessarily has imperfect completeness.

## Proof sketch

In each connected component, fix a vertex and try each of its $L$ labels. A label at one vertex determines the labels of all neighbours through the bijections, so a breadth-first propagation either reaches a consistent labelling of the component or finds a contradiction; the component is satisfiable iff some initial label succeeds.

## Depends on

- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)
- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)
- [The word-RAM model](../../fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- S. Khot, "On the Unique Games Conjecture", IEEE Conference on Computational Complexity, 2010.
- S. Khot, "On the Power of Unique 2-Prover 1-Round Games", STOC 2002.
