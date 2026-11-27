# Williams: time t can be simulated in space √(t log t)

For every time bound $t(n)\ge n$ and every injective binary encoding of instances,

$$
\mathsf{DTIME}(t(n))\subseteq\mathsf{DSPACE}\Bigl(\sqrt{t(n)\,\log t(n)}\Bigr)
$$

for multi-tape Turing machines (space counted in visited work cells, read-only input). No time-constructibility or monotonicity of $t$ is needed.

## Proof sketch

Partition the computation into $t/b$ time blocks of length $b$ and view the dependencies between blocks (Hopcroft–Paul–Valiant block-respecting computation) as a tree-evaluation instance of depth about $t/b$ and fan-in $O(1)$ over an alphabet of $2^{O(b)}$; evaluate it with the Cook–Mertz algorithm in space $O(b\cdot\text{fanin}+ (t/b)\log b)$, and choose $b=\sqrt{t\log t}$.

## Depends on

- [Deterministic time classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Deterministic space classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Time classes are contained in space classes](../../time-and-space-classes-on-multi-tape-machines/dtime-subset-dspace.md)
- [Cook–Mertz: Tree Evaluation is in space O(log n · log log n)](../tree-evaluation/tree-evaluation-in-small-space.md)

## Sources

- Ryan Williams, "Simulating Time With Square-Root Space", Proceedings of the 57th Annual ACM Symposium on Theory of Computing (STOC 2025), 2025, Theorem 1.1.
- John Hopcroft, Wolfgang Paul and Leslie Valiant, "On Time Versus Space", Journal of the ACM 24(2), 1977.
