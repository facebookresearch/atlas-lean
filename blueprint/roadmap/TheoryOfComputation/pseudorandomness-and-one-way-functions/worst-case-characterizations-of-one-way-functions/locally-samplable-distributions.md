# Locally samplable distributions on truth tables

For a function $t=t(N)$, a **$t$-local sampler** is a family of algorithms $S_N$ that take a random seed $r$ (with random access) and output a string $T=S_N(r)\in\{0,1\}^N$ such that each output bit $T_i$ is computed from $i$ in time at most $t$ with random access to $r$; in particular each output bit depends on at most $t$ bits of $r$. A distribution family is **$t$-locally samplable** if it is the output distribution of a $t$-local sampler on a uniformly random seed. Typical uses take $N=2^n$ (truth tables of $n$-variable functions) and $t=N^{\delta}$ or smaller. The uniform distribution and distributions induced by pseudorandom function families are $t$-locally samplable for small $t$, and for most pairs of natural $\mathsf{NP}$-complete problems there are local reductions, so hardness on some locally samplable distribution transfers between them.

## Depends on

- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)

## Sources

- Rahul Ilango, Hanlin Ren and Rahul Santhanam, "Robustness of Average-Case Meta-Complexity via Pseudorandomness", STOC (2022).
