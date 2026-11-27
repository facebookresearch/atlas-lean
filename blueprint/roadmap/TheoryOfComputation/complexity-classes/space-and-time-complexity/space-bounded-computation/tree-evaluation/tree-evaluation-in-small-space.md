# Cook–Mertz: Tree Evaluation is in space O(log n · log log n)

Binary Tree Evaluation with height $H$ and value length $\ell$ is computable by a deterministic multi-tape Turing machine in space

$$
O\bigl((\ell+H+1)\log(\ell+2)+\log(n+2)\bigr),
$$

where $n$ is the length of the encoded instance (the output is not charged). On nontrivial instances ($\ell,H\ge 1$) this is $O(\log n\cdot\log\log n)$. More generally, Tree Evaluation with fan-in $d$, height $H$ and value length $\ell$ is computable in space $O\bigl((H+d\ell)\log(d\ell)\bigr)$ plus the $O(\log n)$ needed to address the input.

## Proof sketch

Run the register procedure over a prime field of size $\mathrm{poly}(\ell)$: the recursion has depth $H$, each frame stores only a round index and a child index ($O(\log\ell)$ bits), and the registers occupy $O(\ell\log\ell)$ bits shared by all levels. Reading a gate's truth-table entry needs the address of the current node, maintained from the recursion stack in $O(H+\log n)$ bits.

## Depends on

- [The Tree Evaluation problem](tree-evaluation-problem.md)
- [Deterministic space classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [The Cook–Mertz register procedure for Tree Evaluation](cook-mertz-register-procedure.md)

## Sources

- James Cook and Ian Mertz, "Tree Evaluation is in Space O(log n · log log n)", Proceedings of the 56th Annual ACM Symposium on Theory of Computing (STOC 2024), pp. 1268–1278 (ECCC TR23-174, Theorems 1, 10 and 18).
