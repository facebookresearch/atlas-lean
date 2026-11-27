# EXACT INDEPENDENT SET is DP-complete

$\mathrm{EXACT\text{-}INDSET}=\{\langle G,k\rangle : \text{the independence number of } G \text{ is exactly } k\}$ is $\mathsf{DP}$-complete under polynomial-time many-one reductions.

## Proof sketch

Membership: $\alpha(G)\ge k$ is in NP and $\alpha(G)\le k$ ($\alpha(G)< k+1$) is in coNP. Hardness: reduce SAT–UNSAT; map $(\varphi,\psi)$ to graphs $G_\varphi,G_\psi$ via the standard reduction to independent set, normalized so that $\alpha=m$ when satisfiable and $m-1$ otherwise, and combine them so that $\alpha$ equals a target exactly when $\varphi$ is satisfiable and $\psi$ is not.

## Depends on

- [The difference class DP and the Boolean hierarchy over NP](dp-and-boolean-hierarchy.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [UNSAT is coNP-complete](../../../completeness-other-classes/unsatisfiability/unsat-conp-complete.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 5, Exercise 8.
- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994.
