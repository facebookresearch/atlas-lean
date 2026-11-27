# Local lemma for $k$-SAT

Let $\varphi$ be a CNF formula in which every clause has exactly $k$ literals on distinct variables, and every clause shares a variable with at most $d$ other clauses. If $e(d+1) \le 2^k$ then $\varphi$ is satisfiable. Under a uniformly random assignment each clause is violated with probability exactly $2^{-k}$, and the violation event of a clause is mutually independent of the events of clauses sharing no variable with it.

## Proof sketch

Apply the symmetric Lovász Local Lemma to the violation events: each has probability $p = 2^{-k}$ and depends on at most $d$ others, and $e p (d+1) \le 1$.

## Depends on

- [CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [Symmetric Lovász Local Lemma](../../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-symmetric-finite.md)

## Sources

- N. Alon and J. H. Spencer, The Probabilistic Method, 4th ed., Wiley, 2016, Chapter 5 (symmetric local lemma and its $k$-SAT corollary).
- P. Erdős and L. Lovász, "Problems and Results on 3-Chromatic Hypergraphs and Some Related Questions", in Infinite and Finite Sets, Colloquia Mathematica Societatis János Bolyai 10, 609–627, 1975.
- R. A. Moser and G. Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), Article 11, 2010.
