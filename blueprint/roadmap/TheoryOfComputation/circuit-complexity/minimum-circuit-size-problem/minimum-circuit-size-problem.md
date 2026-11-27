# The Minimum Circuit Size Problem MCSP and Gap-MCSP

*MCSP* is the language of pairs $(T, s)$ where $T \in \{0,1\}^{2^n}$ is the truth table of a function $f$ with $\mathrm{CC}(f) \le s$. For a size function $s(n)$, $\mathrm{MCSP}[s]$ is the language of truth tables $T$ of $n$-variable functions with $\mathrm{CC}(f) \le s(n)$. For $s_1 \le s_2$, the promise problem $\mathrm{Gap\text{-}MCSP}[s_1, s_2]$ has yes-instances the truth tables with $\mathrm{CC}(f) \le s_1(n)$ and no-instances those with $\mathrm{CC}(f) > s_2(n)$.

## Depends on

- [Circuit complexity of a Boolean function and truth tables](circuit-complexity-of-a-boolean-function.md)

## Sources

- V. Kabanets and J.-Y. Cai, "Circuit Minimization Problem", STOC 2000.
- I. C. Oliveira, J. Pich and R. Santhanam, "Hardness Magnification near State-Of-The-Art Lower Bounds", Computational Complexity Conference (CCC) 2019.
