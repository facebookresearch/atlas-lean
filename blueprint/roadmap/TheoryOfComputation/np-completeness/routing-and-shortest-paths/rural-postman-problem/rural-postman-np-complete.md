# RURAL POSTMAN is NP-complete

The RURAL POSTMAN decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)`, a length `l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a subset `E' ⊆ E`, and a positive integer `B`. Question: is there a circuit in `G` that includes each edge in `E'` and that has total length no more than `B`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN.
- J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems", Networks 6 (1976), 273-280, doi:10.1002/net.3230060305 (Theorem: the rural postman problem is polynomial complete for undirected and for directed graphs).
