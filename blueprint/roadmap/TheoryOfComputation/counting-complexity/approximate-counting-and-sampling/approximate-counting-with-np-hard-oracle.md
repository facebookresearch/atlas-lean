# Approximate counting for PC relations with an NP-hard domain oracle

Let $R\in\mathsf{PC}$ be a relation whose decision problem $S_R$ is $\mathsf{NP}$-hard. Then for every polynomial $q$ there is a probabilistic polynomial-time oracle machine with oracle $S_R$ that on input $x$ outputs a value within a factor $1\pm1/q(|x|)$ of $|R(x)|$ with probability at least $1-2^{-|x|}$.

## Proof sketch

Stockmeyer's hashing argument approximates $|R(x)|$ to within a constant factor using an NP oracle, which reduces to $S_R$; running it on the relation of $k$-tuples of witnesses sharpens the factor to $1\pm1/q$ since $|R^{k}(x)|=|R(x)|^{k}$; repetition and the median reduce the failure probability.

## Depends on

- [Self-reducible search problems (Goldreich's PC and PF)](../../complexity-classes/structural-complexity/search-problems-and-self-reducibility/self-reducible-search-problems.md)
- [Polynomial time with an oracle](../../complexity-classes/time-and-space-complexity-classes/pwith-oracle.md)

## Proof depends on

- [Stockmeyer: approximate counting of #P functions in BPP^NP](../stockmeyer-approximate-counting.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 6.39 (stated there for PC-complete $R$; the proof only uses that the NP oracle of Stockmeyer's procedure reduces to $S_R$).
