# Algebraic laws and separator conditioning for partition functions

Partition functions are multiplicative over instances with disjoint variable sets, invariant under injective relabelling of variables, and compatible with semiring homomorphisms $h$: $Z_{h \circ \mathrm{wt}}(F) = h(Z_{\mathrm{wt}}(F))$. If $S$ is a set of variables separating the variables of $F$ into parts such that every constraint lies within one part together with $S$, then $Z(F) = \sum_{\tau : S \to D} \prod_{\text{parts } P} Z(F_P \restriction \tau)$, where $F_P \restriction \tau$ is the subinstance of part $P$ with $S$ pinned to $\tau$. Moreover $Z(F) \le \prod_{c \in F} \max \mathrm{wt}_c \cdot |D|^{|\mathrm{vars}(F)|}$ over ordered semirings.

## Proof sketch

Distributivity of the semiring and rearrangement of the finite sum over assignments split by their restriction to $S$.

## Depends on

- [Partition function of a weighted CSP](partition-function-of-a-weighted-csp.md)

## Sources

- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, Parameterized Algorithms, Springer, 2015.
