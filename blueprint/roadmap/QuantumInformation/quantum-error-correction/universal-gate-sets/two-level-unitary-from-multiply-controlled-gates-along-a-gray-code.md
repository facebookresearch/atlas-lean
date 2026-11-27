# A two-level unitary from multiply controlled gates along a Gray code

Let $n \ge 1$ and let $T$ be a two-level unitary (a unitary that is [two-level](../../../LinearAlgebra/not-yet-classified/two-level/is-two-level.md)) on $(\mathbb{C}^2)^{\otimes n}$
acting on the computational basis states $|x\rangle$ and $|y\rangle$, $x \ne y \in \{0, 1\}^n$. Let
$x = g_1, g_2, \dots, g_m = y$ be a shortest Gray code from $x$ to $y$: consecutive strings differ in exactly one bit
and each bit in which $x$ and $y$ differ is flipped exactly once, so the strings are distinct and $m - 1 \le n$ is the
Hamming distance of $x$ and $y$. Then $T$ is a product of $2m - 3 \le 2n - 1$ gates, each a multiply controlled gate $\wedge_{n-1}(V)$
acting on the bit where two consecutive strings differ, with its $n - 1$ controls conjugated by single-qubit NOT gates on
the controls that must be $0$. The first $m - 2$ gates are such controlled NOTs, swapping $|g_1\rangle$ with
$|g_2\rangle$, then $|g_2\rangle$ with $|g_3\rangle$, up to $|g_{m-2}\rangle$ with $|g_{m-1}\rangle$; the next applies
the $2 \times 2$ block of $T$ to $|g_{m-1}\rangle$ and $|g_m\rangle$ (in the right order of the two states); the last
$m - 2$ undo the swaps in reverse order. With [multiply controlled gates](multiply-controlled-unitary-from-cnot-and-single-qubit-gates.md)
of $O(n^2)$ gates each, $T$ costs $O(n^3)$ single-qubit gates and CNOTs.

## Depends on

- [Two-level matrix](../../../LinearAlgebra/not-yet-classified/two-level/is-two-level.md)

## Proof depends on

- [Multiply controlled unitaries from CNOT and single-qubit gates](multiply-controlled-unitary-from-cnot-and-single-qubit-gates.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 8 (the Gray code $00111010, \dots, 00100111$, the permutations $(1,2), \dots, (m-2, m-1)$, the modified $\wedge_{n-1}(U)$ on states $m - 1$ and $m$, "Each $T(x_1, x_2)$ involves $2m - 3$ (modified) $\wedge_{n-1}$ gates ... $m$ ... cannot exceed $n + 1$").
