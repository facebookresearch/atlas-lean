# KERNEL is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a directed graph on $\{0, \dots, n - 1\}$, given by a list of distinct loopless arcs, decide whether it has a kernel: an independent set $S$ of vertices such that every vertex outside $S$ has an arc into $S$.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT57] KERNEL.
- V. Chvátal, "On the computational complexity of finding a kernel", Report CRM-300, Centre de recherches mathématiques, Université de Montréal (1973) (the author's reconstruction of the proof: https://users.encs.concordia.ca/~chvatal/kernel.html).
- A. S. Fraenkel, "Planar kernel and Grundy with d ≤ 3, d_out ≤ 2, d_in ≤ 2 are NP-complete", Discrete Applied Mathematics 3 (1981), 257-262, doi:10.1016/0166-218X(81)90003-2.
