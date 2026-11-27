# Pseudodeterministic constructions for dense properties, everywhere and infinitely often

A language $Q\subseteq\{0,1\}^*$ with slices $Q_n=Q\cap\{0,1\}^n$ is **dense** if there is a constant $\rho\ge 1$ with $|Q_n|\ge n^{-\rho}\cdot 2^n$ for every $n\ge 1$, and **easy** if $Q\in\mathrm{P}$.

A **pseudodeterministic construction** for $Q$ is a probabilistic algorithm $B$ together with strings $x_n\in Q_n$ such that $\Pr[B(1^n)=x_n]\ge 2/3$ for every $n$. It is **infinitely-often** pseudodeterministic if, for every $n\ge 1$,

$$
\Pr\bigl[B(1^n)\notin\{x_n,\bot\}\bigr]\le 2^{-n},
$$

and for infinitely many $n$ we have $\Pr[B(1^n)=x_n]\ge 1-2^{-n}$. Thus on every length $B$ never commits to a non-canonical answer, and on infinitely many lengths it succeeds.

## Depends on

- [Pseudodeterministic algorithms for search problems (Gat–Goldwasser)](pseudodeterministic-algorithm-for-search-problem.md)

## Sources

- Igor C. Oliveira and Rahul Santhanam, "Pseudodeterministic Constructions in Subexponential Time", STOC (2017), ECCC TR16-196.
- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
