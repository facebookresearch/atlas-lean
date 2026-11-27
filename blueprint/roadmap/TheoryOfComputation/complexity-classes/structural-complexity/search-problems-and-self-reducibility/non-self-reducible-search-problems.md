# Search problems in PC that are not self-reducible

(i) If $\mathsf{P}\ne\mathsf{NP}\cap\mathsf{coNP}$, there is a total relation $R\in\mathsf{PC}$ that is not in $\mathsf{PF}$ and hence not self-reducible. (ii) If factoring is hard (no polynomial-time function outputs a non-trivial divisor of every composite), then the divisor relation $\{(N,d): 1< d< N,\ d\mid N\}$ is in $\mathsf{PC}$ but not self-reducible, because its decision problem (compositeness) is in $\mathsf{P}$. (iii) Consequently self-reducibility is not a property of the decision problem: under (ii), the relations $\{(N,N): N\text{ composite}\}$ and the divisor relation have the same domain, the first self-reducible and the second not.

## Proof sketch

(i) For $L\in(\mathsf{NP}\cap\mathsf{coNP})\setminus\mathsf{P}$ with witness relations $R_1,R_0$, the total relation $\{(x,(b,w)): (x,w)\in R_b\}$ is in PC, and solving it decides $L$; its domain is everything, so oracle access to it is useless. (ii) An oracle for compositeness is simulable by AKS, so self-reducibility would give a polynomial-time divisor finder.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](self-reducible-search-problems.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)

## Proof depends on

- [PRIMES is in P](../../../polynomial-time-problems/aks-primality-test/primes-in-p.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercises 2.14, 2.16, 2.17.
