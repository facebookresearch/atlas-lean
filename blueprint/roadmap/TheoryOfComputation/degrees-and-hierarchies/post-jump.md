# Post's theorem: $\Delta_{n+1}$ sets and the jump

For $A \subseteq \mathbb{N}$, the jump $A'$ is the halting set of the universal oracle machine with oracle $A$: $e \in A'$ when the $e$-th oracle program, run with oracle $A$, halts on input $e$. Write $\emptyset^{(n)}$ for the $n$-th iterate of the jump starting from the empty set, so $\emptyset^{(0)} = \emptyset$ and $\emptyset^{(n+1)} = (\emptyset^{(n)})'$. The class $\Delta_k$ of the arithmetical hierarchy is $\Sigma_k \cap \Pi_k$.

The following holds: for every $n \in \mathbb{N}$ and every $A \subseteq \mathbb{N}$,

$$A \in \Delta_{n+1} \iff A \le_T \emptyset^{(n)},$$

where $\le_T$ is Turing reducibility.

## Sources

- R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Ch. IV §2, p. 64 (Post's theorem and the hierarchy theorem).
- H. Rogers, *Theory of Recursive Functions and Effective Computability*, §13.4.
