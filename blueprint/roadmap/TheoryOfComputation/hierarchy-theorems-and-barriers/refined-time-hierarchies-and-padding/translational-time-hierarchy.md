# Deterministic time hierarchy with sub-logarithmic gaps by translation

On binary words with multi-tape machines: for every integer $a\ge1$ and real $\varepsilon>0$, if $g(n)\ge n^{a}(\ln n)^{\varepsilon}$ eventually then $\mathsf{DTIME}(n^{a})\subsetneq\mathsf{DTIME}(g)$; and if $g(n)\ge 2^{n}n^{\varepsilon}$ eventually then $\mathsf{DTIME}(2^{n})\subsetneq\mathsf{DTIME}(g)$. These sharpen the $t\log t$ gap of the classical hierarchy at the polynomial and exponential levels.

## Proof sketch

Start from a hierarchy with a polylogarithmic gap at a suitably slower base bound and translate it upward by padding: a collapse $\mathsf{DTIME}(n^a)=\mathsf{DTIME}(g)$ would, applied to padded versions of languages, collapse two classes that the base hierarchy separates.

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [Deterministic time hierarchy: quadratic versus linear time](../time-hierarchy-theorem/time-hierarchy.md)
- [Padding: upward translation of class collapses](padding-translates-collapses.md)

## Sources

- Lance Fortnow and Rahul Santhanam, "Recent Work on Hierarchies for Semantic Classes", ACM SIGACT News 37(3), 2006, Lemma 5 (translation method).
