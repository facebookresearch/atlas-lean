# Macro strings over an alphabet and a range of pointers

A macro symbol is a letter $a \in \mathbb{N}$ or a pointer $p_{j+1}$ with index $j \in \mathbb{N}$. For $k, m \in \mathbb{N}$, a macro string $u$ is over $(k, m)$ when every letter in $u$ is below $k$ and every pointer in $u$ is one of $p_1, \dots, p_m$ (its index is below $m$). In particular the empty string is over every $(k, m)$.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA COMPRESSION, p. 231.
- J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
