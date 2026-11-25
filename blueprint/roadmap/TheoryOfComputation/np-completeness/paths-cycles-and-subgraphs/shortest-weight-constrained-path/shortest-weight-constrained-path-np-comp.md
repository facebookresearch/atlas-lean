# SHORTEST WEIGHT-CONSTRAINED PATH is NP-complete

The SHORTEST WEIGHT-CONSTRAINED PATH decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)`, a length `l(e) ∈ ℤ⁺` and a weight `w(e) ∈ ℤ⁺` for each `e ∈ E`, specified vertices `s, t ∈ V`, and positive integers `K, W`. Question: is there a simple path in `G` from `s` to `t` with total weight `W` or less and total length `K` or less?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND30] SHORTEST WEIGHT-CONSTRAINED PATH (attributed there to N. Megiddo, 1977, private communication; transformation from PARTITION).
