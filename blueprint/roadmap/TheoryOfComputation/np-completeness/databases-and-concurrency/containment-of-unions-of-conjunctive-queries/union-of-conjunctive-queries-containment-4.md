# UNION OF CONJUNCTIVE QUERIES CONTAINMENT is NP-complete

The UNION OF CONJUNCTIVE QUERIES CONTAINMENT decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: two unions of conjunctive queries `U₁ = Q₁ ∪ ⋯ ∪ Qₖ` and `U₂ = Q'₁ ∪ ⋯ ∪ Q'ₗ` (`k, l ≥ 1`) over one relational schema, all heads of the same arity. Question: is `U₁` contained in `U₂` over all database instances, that is, `U₁(D) ⊆ U₂(D)` for every database `D`, where `U(D)` is the union of the answers `Q(D)` of the conjunctive queries `Q` of `U`?

## Sources

- Y. Sagiv and M. Yannakakis, "Equivalences among relational expressions with the union and difference operators", Journal of the ACM 27(4) (1980), 633-655, doi:10.1145/322217.322221 (a union of conjunctive queries is contained in another exactly when each of its conjunctive queries is contained in one of the other's).
- M. Abo Khamis, P. G. Kolaitis, H. Q. Ngo and D. Suciu, "Bag query containment and information theory", Proceedings of the 39th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2020), 95-112, doi:10.1145/3375395.3387645, arXiv:1906.09727 (Section 1: under set semantics, containment "is NP-complete for unions of conjunctive queries", credited to Sagiv and Yannakakis).
