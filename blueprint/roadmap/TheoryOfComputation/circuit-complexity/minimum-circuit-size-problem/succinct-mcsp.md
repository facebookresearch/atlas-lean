# Succinct MCSP

*Succinct MCSP* is the language of tuples $(1^n, s, (x_1, b_1), \dots, (x_t, b_t))$ with $x_i \in \{0,1\}^n$, $b_i \in \{0,1\}$, such that some De Morgan circuit of size at most $s$ maps each $x_i$ to $b_i$ (contradictory samples give a no-instance). When the samples list $f$ on a set $S$, the question is whether $\mathrm{CC}_S(f) \le s$. Its instances can be exponentially shorter than truth tables; it is in NP for polynomially bounded thresholds, because a circuit of size $s$ is a certificate of length $O(s\log s)$.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](minimum-circuit-size-problem.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- I. C. Oliveira, J. Pich and R. Santhanam, "Hardness Magnification near State-Of-The-Art Lower Bounds", Computational Complexity Conference (CCC) 2019.
- I. C. Oliveira and R. Santhanam, "Hardness Magnification for Natural Problems", FOCS 2018.
