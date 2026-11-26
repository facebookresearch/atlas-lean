# UNION OF CONJUNCTIVE QUERIES CONTAINMENT is NP-complete

The UNION OF CONJUNCTIVE QUERIES CONTAINMENT decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: two unions of conjunctive queries $U_1 = Q_1 \cup \cdots \cup Q_k$ and $U_2 = Q'_1 \cup \cdots \cup Q'_l$ with $k, l \ge 1$. The queries are constant-free: every head entry and every argument of a body atom is a variable, variables and relation names being natural numbers. They are over one relational schema, that is, each relation name occurs with a single arity in the body atoms of all the queries; all heads have the same arity; and each query is range-restricted: every variable of its head occurs in some body atom of that query. Question: is $U_1$ contained in $U_2$ over all database instances, that is, $U_1(D) \subseteq U_2(D)$ for every database $D$ giving each relation name a finite set of tuples of natural numbers, where $U(D)$ is the union of the answers $Q(D)$ of the conjunctive queries $Q$ of $U$?

## Sources

- Y. Sagiv and M. Yannakakis, "Equivalences among relational expressions with the union and difference operators", Journal of the ACM 27(4) (1980), 633-655, doi:10.1145/322217.322221 (a union of conjunctive queries is contained in another exactly when each of its conjunctive queries is contained in one of the other's).
- M. Abo Khamis, P. G. Kolaitis, H. Q. Ngo and D. Suciu, "Bag query containment and information theory", Proceedings of the 39th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2020), 95-112, doi:10.1145/3375395.3387645, arXiv:1906.09727 (Section 1: under set semantics, containment "is NP-complete for unions of conjunctive queries", credited to Sagiv and Yannakakis).
