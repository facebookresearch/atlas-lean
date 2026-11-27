# Bhangale–Khot–Minzer: satisfiable 3-CSPs and the role of linear structure

A set $H \subseteq \Sigma \times \Phi \times \Gamma$ of finite alphabets, with coordinate projections $\Sigma_0, \Phi_0, \Gamma_0$, **admits a linear embedding** if there are an abelian group $(G, +)$ and maps $\sigma : \Sigma_0 \to G$, $\phi : \Phi_0 \to G$, $\gamma : \Gamma_0 \to G$, not all constant, with $\sigma(x) + \phi(y) + \gamma(z) = 0$ for every $(x, y, z) \in H$. It is **semirich** if for every $(x, y) \in \Sigma_0 \times \Phi_0$ some $z$ has $(x, y, z) \in H$, and for every $(x, z) \in \Sigma_0 \times \Gamma_0$ some $y$ has $(x, y, z) \in H$. For a distribution $\nu$ on $\Phi$ and $\rho \in [0,1]$ let $T_\rho$ be the noise operator that keeps each coordinate with probability $\rho$ and otherwise resamples it from $\nu$, and $\mathrm{Stab}_\rho(g) = \langle g, T_\rho g \rangle$ on $L^2(\Phi^n, \nu^{\otimes n})$.

**Analytic lemma.** For every $m \in \mathbb{N}$ and $\varepsilon, \alpha > 0$ there are $\xi, \delta > 0$ such that the following holds. Let $\mu$ be a distribution on $\Sigma \times \Phi \times \Gamma$ with $|\Sigma|, |\Phi|, |\Gamma| \le m$, every atom of probability at least $\alpha$, marginals of full support, and support that is semirich and admits no linear embedding. If $f : \Sigma^n \to [-1,1]$, $g : \Phi^n \to [-1,1]$, $h : \Gamma^n \to [-1,1]$ and at least one of $\mathrm{Stab}_{1-\xi}(f), \mathrm{Stab}_{1-\xi}(g), \mathrm{Stab}_{1-\xi}(h)$ (with respect to the corresponding marginal of $\mu$) is at most $\delta$, then

$$
\mathbb{E}_{(x,y,z) \sim \mu^{\otimes n}} \bigl[ f(x)g(y)h(z) \bigr] \le \varepsilon .
$$

**Dictatorship test.** Let $P \subseteq \Sigma^3$ be a predicate that admits no linear embedding and is semirich, and suppose some instance of $P$-CSP has a $(1, s)$ integrality gap for the basic SDP relaxation with an optimal SDP solution all of whose local distributions have semirich supports admitting no linear embedding. Then for every $\varepsilon > 0$ there is a dictatorship test for $P$ with perfect completeness and soundness $s + \varepsilon$. The source proves only the test; it presents such tests as the inner step towards hardness on satisfiable instances assuming the Rich $2$-to-$1$ Games Conjecture of Braverman–Khot–Minzer, with no loss in completeness.

## Proof sketch

The lemma is proved by enlarging the support of $\mu$, adding satisfying triples while keeping it semirich and free of linear embeddings and changing the expectation by little, until the support is the solution set of an equation over a non-abelian group with no non-trivial one-dimensional representation, where the expectation is small. The test follows Raghavendra's construction from the integrality-gap instance without losing completeness; the lemma shows that the high-degree part of a function far from a dictator contributes little to the acceptance probability, and the low-degree part is rounded as in Raghavendra's analysis to an assignment of value at most $s$.

## Sources

- A. Bhangale, S. Khot, D. Minzer, "On approximability of satisfiable k-CSPs: I", STOC (2022), ECCC TR22-061.
