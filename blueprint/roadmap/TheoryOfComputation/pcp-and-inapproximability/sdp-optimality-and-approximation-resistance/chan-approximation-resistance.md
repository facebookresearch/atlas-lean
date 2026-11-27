# Chan: unconditional approximation resistance from pairwise-independent subgroups

Let $G$ be a finite abelian group and $P \subseteq G^k$ a predicate that contains a subgroup $H \le G^k$ whose uniform distribution is balanced pairwise independent. Then $P$ is approximation resistant under NP-hardness: for every $\varepsilon > 0$ it is NP-hard to distinguish Max-$P$ instances with value at least $1 - \varepsilon$ from those with value at most $|P|/|G|^k + \varepsilon$. Consequently, Max-$k$-CSP over the Boolean domain is NP-hard to approximate within $O(k/2^k)$, matching the best algorithms up to a constant factor, and the same holds over any domain when $k$ exceeds the domain size.

## Proof sketch

The key new ingredient is a soundness-reduction technique inspired by XOR lemmas: starting from a label-cover instance with moderate soundness, take the direct sum of independent copies of an inner test whose queries form cosets of $H$; a Fourier-analytic argument over $G$ shows that the advantage over random of any strategy decays multiplicatively, which avoids the Unique Games Conjecture and gives near-optimal soundness for the subgroup predicate.

## Depends on

- [Approximation-resistant predicates and balanced pairwise independence](approximation-resistance.md)

## Proof depends on

- [Hastad: optimal inapproximability of MAX-3SAT](../approximability-of-max-3sat/hastad-max3sat-inapproximability.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Sources

- S. O. Chan, "Approximation resistance from pairwise-independent subgroups", Journal of the ACM 63 (2016), STOC (2013), ECCC TR12-110.
- A. Samorodnitsky, L. Trevisan, "Gowers uniformity, influence of variables, and PCPs", SIAM Journal on Computing 39 (2009) 323-360.
