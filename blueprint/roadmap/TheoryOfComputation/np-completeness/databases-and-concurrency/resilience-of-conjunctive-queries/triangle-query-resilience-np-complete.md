# RESILIENCE OF THE TRIANGLE QUERY is NP-complete

The RESILIENCE OF THE TRIANGLE QUERY decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a database `D` with binary relations `R`, `S`, `T`, and an integer `k`. Question: does `D ⊨ q△` hold, and is there a set `Γ` of at most `k` tuples of `D` such that `D - Γ ⊭ q△`?

## Sources

- C. Freire, W. Gatterbauer, N. Immerman and A. Meliou, "The complexity of resilience and responsibility for self-join-free conjunctive queries", Proceedings of the VLDB Endowment 9(3) (2015), 180-191, doi:10.14778/2850583.2850592, Definition 2 (resilience) and Proposition 10 (`RES(q△)` is NP-complete).
- extended version arXiv:1507.00674, Definition 2.1 and Proposition 3.3 (reduction from 3SAT).
