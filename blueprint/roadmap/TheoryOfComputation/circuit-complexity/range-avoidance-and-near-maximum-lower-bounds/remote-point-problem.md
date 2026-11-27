# The remote point problem

For a circuit class $\mathcal{C}$ and $0 < \delta < \frac{1}{2}$, the **$\delta$-remote point problem** for $\mathcal{C}$ is: given a $\mathcal{C}$-circuit $C : \{0,1\}^n \to \{0,1\}^{\ell}$ with $\ell > n$, find $y \in \{0,1\}^{\ell}$ such that

$$
\operatorname{dist}\bigl(y, C(x)\bigr) \ge \delta \ell \quad \text{for every } x \in \{0,1\}^n.
$$

For $\ell \ge n/(1 - H(\delta)) + 1$, solutions exist by a Hamming-ball counting argument. Solving it for the truth-table map produces truth tables that are hard to approximate on a $\delta$-fraction of inputs, i.e. average-case hard functions.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/range-avoidance-problem.md)

## Sources

- Y. Chen, Y. Huang, J. Li, H. Ren, "Range avoidance, remote point, and hard partial truth tables via satisfying-pairs algorithms", STOC (2023), ECCC TR23-072.
