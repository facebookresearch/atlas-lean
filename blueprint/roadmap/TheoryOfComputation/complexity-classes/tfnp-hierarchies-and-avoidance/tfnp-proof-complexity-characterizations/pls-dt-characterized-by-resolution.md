# PLS^dt is characterized by Resolution: PLS^dt(S(F)) = Θ(Res(F))

For every unsatisfiable CNF formula $F$,

$$
\mathsf{PLS}^{dt}(S(F))=\Theta(\mathrm{Res}(F)),
$$

where $\mathrm{Res}(F)$ is the least value of $\log(\text{size})+\text{width}$ over Resolution refutations. Likewise $\mathsf{FP}^{dt}(S(F))=\Theta(\mathrm{TreeRes}(F))$ for tree-like Resolution with depth as degree. Consequently a family of polylogarithmic-width CNFs has $S(F_n)\in\mathsf{PLS}^{dt}$ if and only if it has Resolution refutations of polylogarithmic width and quasipolynomial size, and Resolution lower bounds of this strength place $S(F_n)$ outside $\mathsf{PLS}^{dt}$.

## Proof sketch

From a refutation with lines $D_1,\dots,D_s=\bot$ build a SINK-OF-DAG formulation whose nodes are the lines: starting from $\bot$, which every assignment falsifies, a falsified derived clause has a falsified premise, found by querying the resolved variable, and the potential is the line index; a sink is a falsified axiom, i.e. a solution of $S(F)$. Each step reads $O(\text{width})$ variables. Conversely, from a depth-$d$ formulation over $m$ nodes, the clauses expressing "node $v$ is reached and the decision trees at $v$ take a given path" have width $O(d)$, and the local-search invariants are derivable in Resolution in size polynomial in $m\,2^{O(d)}$.

## Depends on

- [The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt](false-clause-search-problem.md)
- [Resolution refutation](../../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../../../Logic/propositional-logic/resolution-size-and-width/derivation-width.md)
- [The class PLS of polynomial local search problems](../../total-search-problems/the-class-pls-of-polynomial-local-search.md)
- [Query total search problems TFNP^dt, decision-tree formulations and the black-box classes](query-tfnp-and-formulations.md)

## Sources

- Samuel R. Buss, Leszek Aleksander Kołodziejczyk and Neil Thapen, "Fragments of Approximate Counting", Journal of Symbolic Logic (2014).
- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
