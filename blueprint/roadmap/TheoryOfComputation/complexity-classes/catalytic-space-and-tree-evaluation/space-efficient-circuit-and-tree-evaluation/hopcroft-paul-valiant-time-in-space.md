# Hopcroft–Paul–Valiant: multitape time t is simulable in space O(t / log t)

For every time-constructible $t(n)\ge n$,

$$
\mathsf{DTIME}[t]\subseteq\mathsf{DSPACE}\Bigl[O\Bigl(\frac{t}{\log t}\Bigr)\Bigr]
$$

for multitape Turing machines. This was the best simulation of time by space for nearly fifty years, until the square-root-space simulation of Williams via Tree Evaluation.

## Proof sketch

Make the machine block-respecting with blocks of $b=\Theta(\log t)$ steps, during which every head stays within one tape block. The dependence graph whose vertices are the $t/b$ time intervals has bounded in-degree; a pebble corresponds to storing the $O(b)$-bit contents of one tape block, and by the pebbling lemma $O((t/b)/\log(t/b))$ pebbles suffice, giving space $O(t/\log t)$ after guessing (by exhaustive search) the head-movement pattern that defines the graph.

## Depends on

- [Deterministic time classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Deterministic space classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Hopcroft–Paul–Valiant pebbling bound: bounded in-degree DAGs on N vertices need only O(N/log N) pebbles](hopcroft-paul-valiant-pebbling-bound.md)
- [Time classes are contained in space classes](../../time-and-space-classes-on-multi-tape-machines/dtime-subset-dspace.md)

## Sources

- John E. Hopcroft, Wolfgang J. Paul and Leslie G. Valiant, "On Time Versus Space", Journal of the ACM 24(2) (1977), 332-337.
- James Cook and Ian Mertz, "Tree Evaluation Is in Space O(log n · log log n)", STOC (2024), ECCC TR23-174.
