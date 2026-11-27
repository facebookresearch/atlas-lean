# Deterministic time hierarchy with sub-logarithmic gaps by translation

On binary words with multi-tape machines: for every integer $a\ge1$ and real $\varepsilon>0$, if $g(n)\ge n^{a}(\ln n)^{\varepsilon}$ eventually then $\mathsf{DTIME}(n^{a})\subsetneq\mathsf{DTIME}(g)$; and if $g(n)\ge 2^{n}n^{\varepsilon}$ eventually then $\mathsf{DTIME}(2^{n})\subsetneq\mathsf{DTIME}(g)$. These sharpen the $t\log t$ gap of the classical hierarchy at the polynomial and exponential levels.

## Proof sketch

Suppose $\mathsf{DTIME}(n^{a}(\ln n)^{\varepsilon})\subseteq\mathsf{DTIME}(n^{a})$ (we may take $\varepsilon$ rational). Applying the translation lemma with $f_k(n)=\lceil n(\ln n)^{k\varepsilon/a}\rceil$ gives $\mathsf{DTIME}(n^{a}(\ln n)^{(k+1)\varepsilon})\subseteq\mathsf{DTIME}(n^{a}(\ln n)^{k\varepsilon})$ for each $k$, because $f_k(n)^{a}(\ln f_k(n))^{\varepsilon}\ge n^{a}(\ln n)^{(k+1)\varepsilon}$ and $f_k(n)^a=O(n^{a}(\ln n)^{k\varepsilon})$. Chaining $K$ of these inclusions with $K\varepsilon>1$ yields $\mathsf{DTIME}(n^{a}(\ln n)^{K\varepsilon})\subseteq\mathsf{DTIME}(n^{a})$, contradicting the Hartmanis–Stearns hierarchy ($t\log t=o(T)$ with $t=n^a$, $T=n^{a}(\ln n)^{K\varepsilon}$). The exponential case is identical with $f_k(n)=n+\lceil k\varepsilon\log_2 n\rceil$. The survey states the translation lemma and the method, not this corollary.

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [Deterministic time hierarchy: quadratic versus linear time](../time-hierarchy-theorem/time-hierarchy.md)
- [Padding: upward translation of class collapses](padding-translates-collapses.md)

## Sources

- Lance Fortnow and Rahul Santhanam, "Recent Work on Hierarchies for Semantic Classes", ACM SIGACT News 37(3), 2006, Theorem 1 (deterministic hierarchy) and Lemma 5 (translation method).
- Juris Hartmanis and Richard E. Stearns, "On the Computational Complexity of Algorithms", Transactions of the American Mathematical Society 117, 285–306, 1965.
