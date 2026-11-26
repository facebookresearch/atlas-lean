# McKay–Murray–Williams: under NP ⊆ P/poly, MCSP[s] has circuits of size 2^n·poly(n + s)

Assume $\mathrm{NP} \subseteq \mathrm{P/poly}$. Then there is $c$ such that for every $s$, $\mathrm{MCSP}[s]$ on $2^n$-bit truth tables has De Morgan circuits of size $2^n \cdot c\,(n + s(n) + 1)^c$. The circuit is a merge tree: leaves hold the circuit-certificates of individual points, and each internal node merges certificates for the two halves of a subcube into a minimal certificate (a list of small circuits consistent on the subcube) using a polynomial-hierarchy predicate *Circuit-Min-Merge*, which has polynomial-size circuits under the assumption.

## Proof sketch

Circuit-Min-Merge lies in the polynomial hierarchy; $\mathrm{NP} \subseteq \mathrm{P/poly}$ collapses PH into $\mathrm{P/poly}$ (Karp–Lipton style), so each merge gate is a circuit of size $\mathrm{poly}(n + s)$, and the tree has $2^n$ leaves.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- D. McKay, C. D. Murray and R. R. Williams, "Weak Lower Bounds on Resource-Bounded Compression Imply Strong Separations of Complexity Classes", STOC 2019.
- R. M. Karp and R. J. Lipton, "Some Connections between Nonuniform and Uniform Complexity Classes", STOC 1980.
