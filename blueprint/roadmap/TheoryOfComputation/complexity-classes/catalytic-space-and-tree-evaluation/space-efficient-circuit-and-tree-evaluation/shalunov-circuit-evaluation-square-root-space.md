# Shalunov: circuits of size s are evaluated in space O(sqrt(s log s))

Given a fan-in-two Boolean circuit $C$ of size $s$ on $n\le s$ inputs and $x\in\{0,1\}^n$, the value $C(x)$ can be computed in deterministic space

$$
O\bigl(\sqrt{s\log s}\bigr).
$$

Consequently every $f:\{0,1\}^n\to\{0,1\}$ computable by circuits of size $s$ has branching programs of size $2^{O(\sqrt{s\log s})}$, and, since time-$t$ multitape Turing machines have circuits of size $O(t\log t)$, time-$t$ computations can be simulated in space $O(\sqrt{t}\cdot\log t)$, recovering the square-root-space simulation of time up to a logarithmic factor without reasoning about head motions.

## Proof sketch

Apply the partition lemma with $d=2$ and $b=\Theta(\sqrt{s\log s})$: the quotient has in-degree at most $2$ and depth $h\lt 2s/b$. By the quotient-to-Tree-Evaluation reduction and the Cook–Mertz procedure, the space is $O(h\log b+b)=O((s/b)\log s+b)$, which is $O(\sqrt{s\log s})$ at this choice of $b$. A space-$S$ algorithm yields branching programs of size $2^{O(S)}$ for each input length.

## Depends on

- [The Circuit Value Problem](../../../completeness-other-classes/circuit-value-problem/cvp-dec.md)
- [Deterministic space classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Shalunov: a block quotient of a circuit unfolds into a Tree Evaluation instance](circuit-quotient-unfolds-to-tree-evaluation.md)
- [Shalunov's low-degree DAG partition lemma](shalunov-low-degree-dag-partition.md)

## Sources

- Yakov Shalunov, "Improved Bounds on the Space Complexity of Circuit Evaluation", CCC (2026), arXiv:2504.20950.
