# Zero-error average-case devices for MCSP

A *zero-error average-case device* for $\mathrm{MCSP}[s]$ on $n$-variable truth tables maps each $T \in \{0,1\}^{2^n}$ to an answer in $\{0, 1, ?\}$ such that it is never wrong (an answer $b \in \{0,1\}$ means $b = [\mathrm{CC}(f_T) \le s(n)]$) and it answers $?$ on at most a $\delta(n)$ fraction of truth tables. A *one-sided* device accepts every yes-instance and at most a given number of truth tables in total. Families of formulas or circuits implementing such devices are the objects of average-case hardness magnification.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](minimum-circuit-size-problem.md)

## Sources

- I. C. Oliveira and R. Santhanam, "Hardness Magnification for Natural Problems", FOCS 2018.
