# Partition function of a weighted CSP

Let $D$ be a finite domain, $\mathcal{R}$ a commutative semiring and $\mathrm{wt}$ a weighting assigning to every relation symbol $R$ a function $\mathrm{wt}_R : D^{r} \to \mathcal{R}$ on local assignments. The *partition function* of a CSP instance $F$ is

$$Z(F) = \sum_{\sigma : \mathrm{vars}(F) \to D} \ \prod_{(R, \bar v) \in F} \mathrm{wt}_R(\sigma(\bar v)),$$

the sum ranging over the assignments of the occurring variables. With $0/1$ weights $\mathrm{wt}_R = [\,\cdot \in \mathrm{sem}(R)]$ it is the number of solutions; over a declared variable set $X \supseteq \mathrm{vars}(F)$ it is multiplied by $|D|^{|X \setminus \mathrm{vars}(F)|}$.

## Depends on

- [Finite-domain constraint satisfaction problems](../../np-completeness/satisfiability/constraint-satisfaction-encodings/finite-domain-constraint-satisfaction.md)
- [Model count of a CNF formula](../../../Logic/propositional-logic/model-count-preserving-cnf-transformations/model-count.md)

## Sources

- Martin Dyer, Leslie Ann Goldberg and Mark Jerrum, "The Complexity of Weighted Boolean #CSP", SIAM Journal on Computing 38(5), 2009 (partition functions of weighted constraint satisfaction problems).
- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, Parameterized Algorithms, Springer, 2015.
- L. G. Valiant, "The Complexity of Computing the Permanent", Theoretical Computer Science 8(2), 189–201, 1979.
