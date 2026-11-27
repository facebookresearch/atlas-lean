# Formal complexity measures

A *formal complexity measure* on the Boolean functions of $n$ variables is a function $\mu$ from Boolean functions to $\mathbb{R}_{\ge0}$ (or $\mathbb{N}$) such that $\mu(x_i)\le 1$ and $\mu(\neg x_i)\le1$ for every literal, and $\mu(f\wedge g)\le\mu(f)+\mu(g)$ and $\mu(f\vee g)\le\mu(f)+\mu(g)$ for all $f,g$. Complement invariance is not assumed. Formula leaf size is itself a formal complexity measure, and it is the largest one.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences 55(1), 24–35, 1997.
