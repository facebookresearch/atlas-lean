# P is contained in P/poly

If a language $L$ is decided by a Turing machine in time $t(n) \ge n$, then $L$ has Boolean circuits of size $O(t(n)^2)$ on inputs of length $n$; if moreover $t(n)$ is computable from $1^n$ in space $O(\log t(n))$, as it is for every polynomial $t$, these circuits are constructible in space $O(\log t(n))$ from $1^n$. Consequently $\mathsf{P} \subseteq \mathsf{P/poly}$, and indeed every language in $\mathsf{P}$ has logspace-uniform polynomial-size circuits.

## Depends on

- [Polynomial time with polynomial advice](../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Turing machine (statement prerequisite; formal statement exists, page pending)

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009
- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage Learning, 2013
