# SHORTEST PATH with negative lengths is NP-complete

The SHORTEST PATH with negative lengths decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)`, an integer length `l(e) ∈ ℤ` for each `e ∈ E` (negative lengths allowed), an integer `K`, and specified vertices `s, t ∈ V`. Question: is there a simple path in `G` from `s` to `t` whose length (the sum of the lengths of its edges) is `K` or less?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND29] LONGEST PATH, comment (p. 213: "The analogous directed and undirected "shortest path" problems can be solved for arbitrary graphs in polynomial time ..., but are NP-complete if negative lengths are allowed"), and problem [GT39] HAMILTONIAN PATH, comment (the variant with both endpoints specified is NP-complete; all lengths `-1`, `K = 1 - |V|`).
- R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT is NP-complete; Garey and Johnson derive the path variants from it).
