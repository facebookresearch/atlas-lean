# Clustering of low-syndrome strings for codes with small-set boundary expansion

Let $(H_X, H_Z)$ define a CSS code with minimum distance $\delta n$ such that $H_Z$ has *small-set boundary expansion*: there are constants $\gamma, c > 0$ with $|H_Z x| \ge c\, |x|_{\mathrm{red}}$ whenever $|x|_{\mathrm{red}} \le \gamma n$, where $|x|_{\mathrm{red}} = \min_{y \in \mathrm{im} H_X^{T}} |x + y|$. Then for $\eta < c\gamma$, the set $\{x : |H_Z x| \le \eta n\}$ is contained in the union over cosets $L$ of $\mathrm{im} H_X^{T}$ inside $\ker H_Z$ of the Hamming neighbourhoods $N_L = \{x : \mathrm{dist}(x, L) \le (\eta/c) n\}$, and distinct neighbourhoods $N_L, N_{L'}$ are at Hamming distance at least $\delta n - 2(\eta/c)n$.

## Proof sketch

Given $x$ with small syndrome, a greedy decoding argument using expansion shows that the reduced weight of $x$ relative to some codeword $z \in \ker H_Z$ is at most $|H_Z x|/c$, provided the starting reduced weight is at most $\gamma n$; iterating from the trivial bound and using that syndrome weight bounds the number of unsatisfied checks yields $\mathrm{dist}(x, z + \mathrm{im} H_X^T) \le (\eta/c) n$. Distinct logical cosets differ by a nontrivial logical operator of weight at least $\delta n$, so the triangle inequality separates the neighbourhoods.

## Depends on

- [CSS code Hamiltonians of quantum LDPC codes](css-code-hamiltonians.md)

## Proof depends on

- [CSS code Hamiltonians of quantum LDPC codes](css-code-hamiltonians.md)

## Sources

- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
- Anthony Leverrier, Gilles Zemor, "Quantum Tanner codes", FOCS (2022); arXiv:2202.13641.
