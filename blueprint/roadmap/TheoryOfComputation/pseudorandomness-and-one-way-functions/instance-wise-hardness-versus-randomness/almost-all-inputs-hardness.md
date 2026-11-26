# Hardness of a multi-output function on almost all inputs for probabilistic time

Let $f\colon\{0,1\}^*\to\{0,1\}^*$ with $|f(x)|=k(|x|)$ and let $T\colon\mathbb{N}\to\mathbb{N}$. A probabilistic algorithm $A$ **computes $f$ on input $x$** if $\Pr_r[A(x,r)=f(x)]\ge 2/3$, where the whole output string must equal $f(x)$.

We say that $f$ **cannot be computed in probabilistic time $T$ on almost all inputs** if for every probabilistic algorithm $A$ running in time $T(|x|)$ there is $n_0\in\mathbb{N}$ such that for **every** $x\in\{0,1\}^*$ with $|x|\ge n_0$ we have $\Pr_r[A(x,r)=f(x)]<2/3$.

This is stronger than the usual requirement that $A$ fail on at least one input of each large length. The infinitely-often variant asks for an infinite set $S\subseteq\mathbb{N}$ such that every $T$-time $A$ fails on every $x$ with $|x|\in S$ and $|x|$ large enough. Hardness for a distribution family $\{X_n\}$ with success bound $\mu$ means that $\Pr_{x\sim X_n}[A \text{ computes } f \text{ on } x]\le\mu$ for all large $n$.

## Depends on

- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Sources

- Lijie Chen and Roei Tell, "Hardness vs Randomness, Revised: Uniform, Non-Black-Box, and Instance-Wise", FOCS (2021), ECCC TR21-080.
