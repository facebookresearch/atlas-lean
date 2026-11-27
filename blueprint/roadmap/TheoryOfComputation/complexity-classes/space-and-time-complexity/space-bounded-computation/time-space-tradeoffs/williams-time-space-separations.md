# Time–space separations from the square-root-space simulation

Let $s$ be space-constructible with $\lfloor\log_2 n\rfloor\le s(n)$ eventually, and let $t$ satisfy $\sqrt{\max(n,t(n))\cdot(\log_2\max(n,t(n))+1)}=o(s(n))$. Then on binary words

$$
\mathsf{DTIME}(t)\subsetneq\mathsf{DSPACE}(s)\quad\text{and}\quad\mathsf{DSPACE}(s)\not\subseteq\mathsf{DTIME}(t).
$$

In particular, if $s(n)\ge n$ eventually then $\mathsf{DTIME}(s^{2-\varepsilon})\subsetneq\mathsf{DSPACE}(s)$ for every real $\varepsilon>0$; $\mathsf{DTIME}(n^a)\subsetneq\mathsf{DSPACE}(n^b)$ whenever $1\le b$ and $a<2b$; and linear space is not contained in $\mathsf{DTIME}(n^{2-\varepsilon})$.

## Proof sketch

By the square-root simulation, $\mathsf{DTIME}(t)\subseteq\mathsf{DSPACE}(s')$ with $s'=o(s)$, and the deterministic space hierarchy gives a language in $\mathsf{DSPACE}(s)\setminus\mathsf{DSPACE}(s')$.

## Depends on

- [Deterministic time classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Deterministic space classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dspace.md)

## Proof depends on

- [Williams: time t can be simulated in space √(t log t)](williams-square-root-space.md)
- [Space hierarchy theorem for space-constructible bounds](../../../../hierarchy-theorems-and-barriers/space-hierarchy-theorem/space-hierarchy-theorem-for-space-constructible.md)

## Sources

- Ryan Williams, "Simulating Time With Square-Root Space", Proceedings of the 57th Annual ACM Symposium on Theory of Computing (STOC 2025), 2025.
- Richard E. Stearns, Juris Hartmanis and Philip M. Lewis II, "Hierarchies of Memory Limited Computations", Proceedings of the 6th Annual Symposium on Switching Circuit Theory and Logical Design, 1965.
