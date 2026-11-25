# SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view) is NP-complete

The SIDE-EFFECT-FREE DELETION PROPAGATION (project-join view) decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a source database, that is, relations `R₁` over `(A, B)` and `R₂` over `(B, C)`, and a tuple `t` of the view `V(R₁, R₂)`. Question: is there a set of source tuples `T₁ ⊆ R₁`, `T₂ ⊆ R₂` whose deletion is side-effect-free: it removes `t` from the view and no other view tuple, i.e. `V(R₁ \ T₁, R₂ \ T₂) = V(R₁, R₂) \ {t}`?

## Sources

- P. Buneman, S. Khanna and W.-C. Tan, "On propagation of deletions and annotations through views", Proceedings of the 21st ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS 2002), 150-158, doi:10.1145/543613.543633 (Section 2.1.1, Theorem 2.1: deciding whether there is a side-effect-free deletion is NP-hard for the project-join query `Π_{A,C}(R₁(A, B) ⋈ R₂(B, C))`).
