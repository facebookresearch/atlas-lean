# The range avoidance problem Avoid and its restriction C-Avoid to a circuit class

**Avoid**: given a Boolean circuit $C\colon\{0,1\}^n\to\{0,1\}^m$ with $m>n$ (the *stretch*), output some $y\in\{0,1\}^m$ such that $C(x)\neq y$ for every $x\in\{0,1\}^n$. Every instance has a solution because $|\mathrm{Im}(C)|\le 2^n<2^m$; the hardest case is $m=n+1$.

For a class $\mathcal{C}$ of multi-output circuits, **$\mathcal{C}$-Avoid** restricts the input to circuits in which every output bit is computed by a $\mathcal{C}$ circuit. In particular, for a constant $k$, **$\mathrm{NC}^0_k$-Avoid** restricts to circuits in which each output bit depends on at most $k$ input bits.

## Depends on

- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Robert Kleinberg, Oliver Korten, Daniel Mitropolsky and Christos Papadimitriou, "Total Functions in the Polynomial Hierarchy", ITCS (2021), LIPIcs 185.
- Oliver Korten, "The Hardest Explicit Construction", FOCS (2021), arXiv:2106.00875.
- Hanlin Ren, Rahul Santhanam and Zhikun Wang, "On the Range Avoidance Problem for Circuits", FOCS (2022), ECCC TR22-048.
