# Pseudodeterministic algorithms for search problems (Gat–Goldwasser)

A search problem is a relation $\Pi\subseteq\{0,1\}^*\times\{0,1\}^*$ with solution sets $\Pi_x=\{y:(x,y)\in\Pi\}$. A probabilistic algorithm $A$ is **pseudodeterministic** for $\Pi$ if for every $x$ with $\Pi_x\neq\emptyset$ there is a single **canonical** solution $s(x)\in\Pi_x$ such that

$$
\Pr_r\bigl[A(x,r)=s(x)\bigr]\ge 2/3 .
$$

Thus, on each input, independent runs of $A$ return the same solution with high probability. **Pseudodeterministic polynomial time** asks for $A$ running in polynomial time. A **pseudodeterministic construction** of a property $Q\subseteq\{0,1\}^*$ is the special case of the search problem with input $1^n$ and solutions the $n$-bit strings in $Q$, typically required only for infinitely many $n$: on input $1^n$ the algorithm outputs a canonical $n$-bit string of $Q$ with probability at least $2/3$.

## Depends on

- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [Search problems: FNP, FP and TFNP](../../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Oded Goldreich, Shafi Goldwasser and Dana Ron, "On the Possibilities and Limitations of Pseudodeterministic Algorithms", ITCS (2013), doi:10.1145/2422436.2422453 (the notion is credited there to Gat and Goldwasser).
- Igor C. Oliveira and Rahul Santhanam, "Pseudodeterministic Constructions in Subexponential Time", STOC (2017), doi:10.1145/3055399.3055500.
- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
