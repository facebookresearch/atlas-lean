# McKay–Murray–Williams hardness magnification for MCSP

If for some $k$ and every $c > 0$ there are infinitely many $n$ such that some $2^n$-bit slice of $\mathrm{MCSP}[n^k]$ requires De Morgan circuits with more than $2^n \cdot c\,(n+1)^c$ gates, then $\mathrm{NP} \not\subseteq \mathrm{P/poly}$, and in particular $\mathrm{P} \ne \mathrm{NP}$. That is, barely superlinear (in $N = 2^n$) circuit lower bounds for MCSP with polynomial thresholds would separate P from NP.

## Proof sketch

Contrapositive of the merge-circuit lemma with $s(n) = n^k$: if $\mathrm{NP} \subseteq \mathrm{P/poly}$, every slice has circuits of size $2^n \mathrm{poly}(n)$.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)

## Proof depends on

- [McKay–Murray–Williams: under NP ⊆ P/poly, MCSP[s] has circuits of size 2^n·poly(n + s)](mckay-murray-williams-merge-circuits.md)

## Sources

- D. McKay, C. D. Murray and R. R. Williams, "Weak Lower Bounds on Resource-Bounded Compression Imply Strong Separations of Complexity Classes", STOC 2019.
