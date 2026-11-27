# Entropy cost of postselecting on checked answers

For a finite tensor strategy with independent full-question laws, consider the reduced state on Alice's side after postselecting on a checked-answer event of Born weight $w > 0$. Then (1) forgetting Bob's checked answers leaves the selected Alice marginal, each branch lies below a common trace-one reference state independent of Bob's question law, and the normalized reduced branch has Umegaki relative entropy at most $\ln(1/w)$ against that reference; (2) with a retained finite label, the restricted Born state has trace equal to the event probability $P$, and for $P > 0$ its normalization has relative entropy at most $\ln|\mathcal{Z}| - \ln P$ against the reference with uniform checked answers and the original label distribution.

## Proof sketch

If $0 \le \rho \le \sigma$ with $\mathrm{tr}\,\rho = w$, then $D(\rho/w \,\|\, \sigma) \le \ln(1/w)$ by operator monotonicity of the logarithm. The checked-answer register adds at most $\ln|\mathcal{Z}|$ since uniform answers dominate any answer distribution up to the factor $|\mathcal{Z}|$.

## Depends on

- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)
- [Conditional entropy of a finite joint law](../../../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
