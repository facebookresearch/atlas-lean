# Search problems in PC that are not self-reducible

Self-reducibility is a property of a search problem, not of the decision problem implicit in it: if factoring is hard (no polynomial-time function outputs a non-trivial divisor of every composite), there are relations $R_1,R_2\in\mathsf{PC}$ with the same implicit decision problem, $\{x:R_1(x)\ne\emptyset\}=\{x:R_2(x)\ne\emptyset\}$, such that $R_1$ is self-reducible and $R_2$ is not.

## Proof sketch

Derived here (the cited source leaves these steps to exercises): (i) take $R_2=\{(N,d): 1<d<N,\ d\mid N\}$ and $R_1=\{(N,N): N\text{ composite}\}$. Both have the set of composites as implicit decision problem, which is in $\mathsf{P}$ by AKS; $R_1\in\mathsf{PF}$ trivially, so it is self-reducible, while an oracle for compositeness is simulable in polynomial time, so self-reducibility of $R_2$ would give a polynomial-time divisor finder. (ii) If $\mathsf{P}\ne\mathsf{NP}\cap\mathsf{coNP}$, there is a total relation $R\in\mathsf{PC}$ that is not in $\mathsf{PF}$ and hence not self-reducible: for $L\in(\mathsf{NP}\cap\mathsf{coNP})\setminus\mathsf{P}$ with witness relations $R_1',R_0'$, the relation $\{(x,(b,w)): (x,w)\in R_b'\}$ is in PC and solving it decides $L$, while its domain is everything, so oracle access to it is useless.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](self-reducible-search-problems.md)

## Proof depends on

- [PRIMES is in P](../../../polynomial-time-problems/aks-primality-test/primes-in-p.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)
- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Section 2.2.3.1, the paragraph before Section 2.2.3.2 ("In general, self-reducibility is a property of the search problem and not of the decision problem implicit in it"), with Exercises 2.14, 2.16 and 2.17.
