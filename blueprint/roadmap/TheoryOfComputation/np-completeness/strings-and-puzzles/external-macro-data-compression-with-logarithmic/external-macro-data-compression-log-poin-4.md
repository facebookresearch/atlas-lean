# EXTERNAL MACRO DATA COMPRESSION with logarithmic pointer cost is NP-complete

For every natural number $k \ge 3$, the decision problem [EXTERNAL MACRO DATA COMPRESSION with
logarithmic pointer cost](external-macro-data-compression-log-poin-3.md) for $k$ belongs to NP,
and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA COMPRESSION, comment (p. 231): "Remains NP-complete even if `h` is any fixed integer 2 or greater. Many variants, including those in which `D` can contain no pointers and/or no pointers can refer to overlapping strings, are also NP-complete. If the alphabet size is fixed at 3 or greater, and the pointer cost is `⌈h·log|s|⌉`, the problem is also NP-complete" (references [Storer, 1977], [Storer and Szymanski, 1978]).
- J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
