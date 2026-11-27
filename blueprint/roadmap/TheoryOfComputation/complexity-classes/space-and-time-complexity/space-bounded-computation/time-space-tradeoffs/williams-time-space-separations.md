# Time–space separations from the square-root-space simulation

For every space-constructible $s$ with $s(n)\ge n$ and every real $\varepsilon>0$, on multitape Turing machines

$$
\mathsf{DSPACE}(s)\not\subseteq\mathsf{DTIME}(s^{2-\varepsilon}).
$$

In particular $\mathsf{DSPACE}(n^b)\not\subseteq\mathsf{DTIME}(n^a)$ whenever $b\ge1$ and $a<2b$, and linear space is not contained in $\mathsf{DTIME}(n^{2-\varepsilon})$ for any $\varepsilon>0$.

## Proof sketch

By the square-root simulation, $\mathsf{DTIME}(t)\subseteq\mathsf{DSPACE}(\sqrt{t\log t})$ for $t(n)\ge n$, and $\sqrt{s^{2-\varepsilon}\log s^{2-\varepsilon}}=o(s)$, so the deterministic space hierarchy gives a language in $\mathsf{DSPACE}(s)$ outside $\mathsf{DTIME}(s^{2-\varepsilon})$.

Derived here (not stated in the cited source) by the same argument: the inclusion is proper, $\mathsf{DTIME}(s^{2-\varepsilon})\subsetneq\mathsf{DSPACE}(s)$ for $0<\varepsilon\le1$; and more generally, for space-constructible $s$ with $\lfloor\log_2 n\rfloor\le s(n)$ eventually and any $t$ with $\sqrt{\max(n,t(n))\cdot(\log_2\max(n,t(n))+1)}=o(s(n))$, $\mathsf{DTIME}(t)\subsetneq\mathsf{DSPACE}(s)$ and $\mathsf{DSPACE}(s)\not\subseteq\mathsf{DTIME}(t)$; for instance $\mathsf{DTIME}(n^a)\subsetneq\mathsf{DSPACE}(n^b)$ whenever $1\le b$ and $a<2b$.

## Depends on

- [Deterministic time classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Deterministic space classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Williams: time t can be simulated in space √(t log t)](williams-square-root-space.md)
- [Space hierarchy theorem for space-constructible bounds](../../../../hierarchy-theorems-and-barriers/space-hierarchy-theorem/space-hierarchy-theorem-for-space-constructible.md)

## Sources

- Ryan Williams, "Simulating Time With Square-Root Space", Proceedings of the 57th Annual ACM Symposium on Theory of Computing (STOC 2025), 2025; arXiv:2502.17779, Theorem 1.1 and Corollary 1.2.
- Richard E. Stearns, Juris Hartmanis and Philip M. Lewis II, "Hierarchies of Memory Limited Computations", Proceedings of the 6th Annual Symposium on Switching Circuit Theory and Logical Design, 1965.
