# Locally samplable distributions on truth tables

For a function $t=t(N)$, a **$t$-local sampler** is a family of algorithms $S_N$ that take a random seed $r$ (with random access) and output a string $T=S_N(r)\in\{0,1\}^N$ such that each output bit $T_i$ is computed from $i$ in time at most $t$ with random access to $r$; in particular each output bit depends on at most $t$ bits of $r$. A distribution family is **$t$-locally samplable** if it is the output distribution of a $t$-local sampler on a uniformly random seed. Typical uses take $N=2^n$ (truth tables of $n$-variable functions) and $t=N^{\delta}$ or smaller. The uniform distribution ($T_i=r_i$) is $O(\log N)$-locally samplable, and a pseudorandom function family $\{F_k\}$ whose value $F_k(i)$ on inputs $i$ of length $\log N$ is computable in time $t$ with random access to the key $k$ induces the $t$-locally samplable distribution $T_i=F_k(i)$ for a uniformly random key $k$.

## Depends on

- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)

## Sources

- Rahul Ilango, Hanlin Ren and Rahul Santhanam, "Robustness of Average-Case Meta-Complexity via Pseudorandomness", STOC (2022).
