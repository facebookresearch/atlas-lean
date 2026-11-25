# UNSAFE LOCKING POLICY is NP-complete

The UNSAFE LOCKING POLICY decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a set `X = {x₁, ..., xₘ}` of variables and a set `T₁, ..., Tₙ` of transactions, each consisting of a sequence of steps of the form `lock(x)`, `update(x)` and `unlock(x)`, where each `update(x)` occurs between a `lock(x)`-`unlock(x)` pair (although not necessarily contiguous to either), and no transaction contains more than one `lock(x)`-`unlock(x)` pair for any `x ∈ X`. Question: is there a "legal" schedule for the transactions that is not serializable, i.e., is there a non-serializable schedule `S` such that between any two occurrences of `lock(x)` in `S` (for any `x ∈ X`), there is an occurrence of `unlock(x)`?

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300, doi:10.1016/0196-6774(83)90028-7, problem [6] UNSAFE LOCKING POLICY (reference: Papadimitriou and Yannakakis; transformation from 3SAT), and Section 3 (serializability).
- C. H. Papadimitriou, "Concurrency control by locking", SIAM J. Comput. 12 (1983), 215-226, doi:10.1137/0212013.
- M. Yannakakis, "A theory of safe locking policies in database systems", J. ACM 29 (1982), 718-740, doi:10.1145/322326.322333.
