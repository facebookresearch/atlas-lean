# Batched lookup and routing circuits from sorting networks

Let $N$ records of $\ell$ bits each carry a $k$-bit key and a tag marking them as sources or queries. Using one Batcher sorting network on the records (comparators acting on whole records and sharing their comparison bit), a broadcast pass along runs of equal keys, and the reversal of the saved comparator decisions, there are De Morgan circuits of size $O(N\log^2N\cdot(k+\ell))$ and depth $O(\log^2N\cdot\log(k+\ell))$ that deliver to every query the value (or the bitwise OR of the values) of the sources with the same key, at the query's original position. In particular a fixed table of $2^a$ entries can be read at $N$ computed addresses with $O\bigl((2^a+N)\log^2(2^a+N)\cdot(a+r)\bigr)$ gates, where $r$ is the bit width of each table entry.

## Proof sketch

After sorting by (key, tag), each query's sources precede it within its key run; a linear-size segmented propagation circuit carries values forward along runs, and running the saved comparator decisions backwards restores the original order of the payloads.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)
- [Batcher's odd-even merge sorting network](../../../../../ComputerScience/sorting-and-searching/sorting-networks/batcher-odd-even-mergesort/odd-even-sorter.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
