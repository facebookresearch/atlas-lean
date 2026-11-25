# STRONG INEQUIVALENCE OF IANOV SCHEMES is NP-complete

The STRONG INEQUIVALENCE OF IANOV SCHEMES decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: finite sets `F` and `P` of function and predicate symbols, a single variable `x`, and two Ianov schemes over `F`, `P` and `x`, each a sequence `I₁, I₂, …, Iₘ` of instructions of the form `x ← f(x)`, `if p(x) then goto Iⱼ else goto Iₖ`, and `halt`, where `f ∈ F` and `p ∈ P`. Question: are the two given Ianov schemes not strongly equivalent, i.e., is there a domain set `D`, an interpretation of each `f ∈ F` as a function `f : D → D`, an interpretation of each `p ∈ P` as a function `p : D → {T, F}`, and an initial value `x₀ ∈ D` for `x`, such that either both schemes halt with different final values for `x` or one halts and the other doesn't?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO16] STRONG INEQUIVALENCE OF IANOV SCHEMES, p. 276 (references [Constable, Hunt, and Sahni, 1974] and [Rutledge, 1964]; transformation from 3SAT).
- R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031 (journal version of the 1974 Cornell report GJ cites: strong equivalence of single variable program schemes is NP-complete).
- J. D. Rutledge, "On Ianov's program schemata", Journal of the ACM 11 (1964), 1-9, doi:10.1145/321203.321204 (membership in NP, per GJ).
