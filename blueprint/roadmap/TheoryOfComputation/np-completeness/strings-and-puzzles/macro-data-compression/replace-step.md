# One pointer-replacement step

A macro symbol is a letter $a \in \mathbb{N}$ or a pointer $p_{j+1}$ with index $j \in \mathbb{N}$. Let $\sigma$ be a pointer assignment, sending every pointer $p$ to a macro string $\sigma(p)$. A macro string $u$ turns into $v$ in one replacement step when $u = x\, p\, y$ and $v = x\, \sigma(p)\, y$ for some macro strings $x, y$ and some pointer $p$: one occurrence of a pointer is replaced by its assigned string, which may itself contain pointers.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA COMPRESSION, p. 231.
- J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
