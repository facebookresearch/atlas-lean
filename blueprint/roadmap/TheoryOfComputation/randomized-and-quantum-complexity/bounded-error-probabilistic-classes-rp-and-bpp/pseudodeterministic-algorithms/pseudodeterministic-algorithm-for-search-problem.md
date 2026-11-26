# Pseudodeterministic algorithms for search problems (Gat–Goldwasser)

A search problem is a relation $\Pi\subseteq\{0,1\}^*\times\{0,1\}^*$ with solution sets $\Pi_x=\{y:(x,y)\in\Pi\}$. A probabilistic algorithm $A$ is **pseudodeterministic** for $\Pi$ if for every $x$ with $\Pi_x\neq\emptyset$ there is a single **canonical** solution $s(x)\in\Pi_x$ such that

$$
\Pr_r\bigl[A(x,r)=s(x)\bigr]\ge 2/3 .
$$

By running $A$ several times and taking the plurality output, the probability can be raised to $1-2^{-|x|}$, so independent runs agree with each other with high probability. **Pseudodeterministic polynomial time** asks for $A$ running in polynomial time. A zero-error variant asks that $A$ output $s(x)$ or a failure symbol $\bot$, never another string.

## Depends on

- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [Search problems: FNP, FP and TFNP](../../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Eran Gat and Shafi Goldwasser, "Probabilistic Search Algorithms with Unique Answers and Their Cryptographic Applications", ECCC TR11-136 (2011).
