# Gelfond–Lifschitz reduct

The reduct $P^M$ of a normal logic program $P$ with respect to a set $M$ of atoms deletes every rule with some negated atom $c_j \in M$ and drops the negative bodies of the remaining rules, leaving the definite rules $a \leftarrow b_1, \dots, b_k$ (as Horn clauses $a \vee \neg b_1 \vee \cdots \vee \neg b_k$).

## Sources

- W. Marek and M. Truszczyński, "Autoepistemic logic", Journal of the ACM 38 (1991), 588-619, doi:10.1145/116825.116836 ("it is proven that the problem of existence of stable models is NP-complete").
- M. Gelfond and V. Lifschitz, "The stable model semantics for logic programming", Logic Programming: Proceedings of the Fifth International Conference and Symposium (ICLP/SLP 1988), MIT Press, 1070-1080.
