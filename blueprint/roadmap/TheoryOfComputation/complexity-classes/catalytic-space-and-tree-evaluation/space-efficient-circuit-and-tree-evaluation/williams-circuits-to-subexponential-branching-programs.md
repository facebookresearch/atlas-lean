# Williams: bounded fan-in circuits of size s have branching programs of size 2^{O(sqrt(s) polylog s)}

There is a universal constant $k\ge 1$ such that for all $s\ge n$, every bounded fan-in Boolean circuit of size $s$ on $n$ inputs has a branching program of size at most

$$
2^{k\sqrt{s}\,\log^{k}s}.
$$

Equivalently, size-$s$ circuits can be evaluated on any input in space $\sqrt{s}\cdot\mathrm{poly}(\log s)$, so arbitrary subquadratic-size circuits are simulated by subexponential-size branching programs.

## Proof sketch

Pippenger's simulation evaluates a size-$s$ circuit on a multitape Turing machine in time $s\cdot\mathrm{poly}(\log s)$. Recall Williams' theorem that time-$t$ multitape machines run in space $O(\sqrt{t\log t})$, obtained by reducing block-respecting computations to implicit Tree Evaluation and applying the Cook–Mertz procedure; composing the two gives space $\sqrt{s}\,\mathrm{poly}(\log s)$, and the branching program bound follows from the standard conversion of space-$S$ machines to programs of size $2^{O(S)}$.

## Depends on

- [The Circuit Value Problem](../../../completeness-other-classes/circuit-value-problem/cvp-dec.md)
- [Deterministic space classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Deterministic time classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Ryan Williams, "Simulating Time With Square-Root Space", STOC (2025), arXiv:2502.17779, ECCC TR25-017.
- Yakov Shalunov, "Improved Bounds on the Space Complexity of Circuit Evaluation", CCC (2026), arXiv:2504.20950.
