# Ackermann's reduction from uninterpreted functions to equality logic

Let $\varphi$ be a quantifier-free formula of equality logic with uninterpreted functions. Replace every occurrence of an application $f(t_1, \dots, t_n)$ by a fresh constant $c_{f(t_1,\dots,t_n)}$ (innermost first), obtaining $\varphi^{\mathrm{flat}}$, and for every pair of applications $f(\bar s)$, $f(\bar t)$ of the same function symbol in $\varphi$ add the functional-consistency constraint $\bigl(\bigwedge_i s'_i = t'_i\bigr) \to c_{f(\bar s)} = c_{f(\bar t)}$, where $s'_i$, $t'_i$ are the flattened arguments. Then $\varphi$ is valid exactly when the implication from the conjunction of all these constraints to $\varphi^{\mathrm{flat}}$ is valid; applied to $\neg\varphi$, this says that the conjunction of $\varphi^{\mathrm{flat}}$ with the constraints is a formula of pure equality logic that is satisfiable if and only if $\varphi$ is.

## Sources

- D. Kroening and O. Strichman, *Decision Procedures: An Algorithmic Point of View*, 2nd ed., Springer, 2016; the authors' course slides for Chapter 4, "Transforming UFs to Equality Logic using Ackermann's reduction", <https://www.decision-procedures.org/slides/uf.pdf>
- R. E. Bryant, S. German and M. N. Velev, "Processor verification using efficient reductions of the logic of uninterpreted functions to propositional logic", *ACM Transactions on Computational Logic* 2(1):93–134, 2001, Section 4.3.1, <https://arxiv.org/abs/cs/9910014>
