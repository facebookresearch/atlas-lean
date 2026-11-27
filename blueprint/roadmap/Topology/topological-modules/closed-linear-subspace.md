# Closed submodule of a module equipped with a topology

Let $R$ be a semiring and let $M$ be an $R$-module, with $M$ a commutative monoid under addition, that also carries a topology; no compatibility between the topology and the module operations is required. A *closed submodule* of $M$ is a submodule $N$ of $M$, that is, a subset of $M$ that contains $0$ and is closed under addition and under multiplication by elements of $R$, such that $N$ is a closed subset of $M$. When $M$ is a normed space over $\mathbb{F} \in \{\mathbb{R}, \mathbb{C}\}$ with the topology of the metric $d(x, y) = \|x - y\|$, the closed submodules of $M$ are its *closed linear subspaces*: the linear subspaces of $M$ that are closed sets.

## Sources

- John B. Conway, A Course in Functional Analysis, 2nd ed., Graduate Texts in Mathematics 96, Springer, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for closed submodules of a module over a semiring that carries a topology, with no continuity condition on the module operations: `ClosedSubmodule`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Algebra/Module/ClosedSubmodule.lean#L31-L39.
