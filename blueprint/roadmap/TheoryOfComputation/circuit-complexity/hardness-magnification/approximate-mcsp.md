# Approximate MCSP

For size thresholds $s_1 \le s_2$ and $\delta \in (0, 1)$, the promise problem $(1, 1 - \delta)\text{-}\mathrm{MCSP}[s_1, s_2]$ has yes-instances the truth tables $T$ of functions with $\mathrm{CC}(f_T) \le s_1$ and no-instances the truth tables such that every circuit of size at most $s_2$ agrees with $f_T$ on at most a $1 - \delta$ fraction of inputs. Gap-MCSP is the case of exact agreement, $\delta = 2^{-n}$.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../minimum-circuit-size-problem/minimum-circuit-size-problem.md)

## Sources

- I. C. Oliveira and R. Santhanam, "Hardness Magnification for Natural Problems", FOCS 2018.
- L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020.
