# The total function class TFΣ2P and the explicit-construction class APEPP

A search problem $\Pi$ is in **$\mathrm{TF}\Sigma_2\mathrm{P}$** if it is total ($\Pi_x\neq\emptyset$ for every $x$), solutions have length polynomial in $|x|$, and the relation $(x,y)\in\Pi$ is decidable in $\mathrm{coNP}$, so that a solution is verified with one universal quantifier.

**$\mathrm{APEPP}$** (Abundant Empty Pigeonhole Principle) is the class of total search problems polynomial-time reducible to Avoid with stretch $m=n+1$: a problem belongs to $\mathrm{APEPP}$ if there are polynomial-time maps $x\mapsto C_x$ and $(x,y)\mapsto g(x,y)$ such that $g(x,y)\in\Pi_x$ whenever $y\notin\mathrm{Im}(C_x)$. Its totality is the dual weak pigeonhole principle: a map $\{0,1\}^n\to\{0,1\}^{n+1}$ is not surjective. Since checking $y\notin\mathrm{Im}(C)$ is a $\mathrm{coNP}$ question, $\mathrm{APEPP}\subseteq\mathrm{TF}\Sigma_2\mathrm{P}$. The larger class $\mathrm{PEPP}$ of Kleinberg, Korten, Mitropolsky and Papadimitriou is based on the empty pigeonhole principle with a single extra hole.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [The universal levels of the polynomial hierarchy](../../time-and-space-complexity-classes/pi-k.md)
- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Robert Kleinberg, Oliver Korten, Daniel Mitropolsky and Christos Papadimitriou, "Total Functions in the Polynomial Hierarchy", ITCS (2021), LIPIcs 185.
- Oliver Korten, "The Hardest Explicit Construction", FOCS (2021), arXiv:2106.00875.
