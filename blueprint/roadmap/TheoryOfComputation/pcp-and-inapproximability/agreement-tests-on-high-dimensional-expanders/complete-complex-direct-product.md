# Direct product testing on the complete complex in the low-soundness regime

Let $\mathcal{F} = \binom{[n]}{k}$ with $n \ge k^2$ and consider the test that samples $s_1, s_2$ uniformly with $|s_1 \cap s_2| = \sqrt{k}$. There is an absolute constant $c$ such that for every $\delta \ge \exp(-c\sqrt[3]{k})$ the following holds: if $\operatorname{Agr}(\{f_s\}) \ge \delta$ then there is $G : [n] \to \Sigma$ such that

$$
\Pr_{s}\Bigl[\Pr_{i \in s}\bigl[f_s(i) \ne G(i)\bigr] \le k^{-c}\Bigr] \ge \Omega(\delta).
$$

Thus the uniform $\sqrt{k}$-intersection test on $k$-subsets is a low-acceptance agreement test, but its set family has size $\binom{n}{k}$, superpolynomial in $n$ for growing $k$.

## Proof sketch

Fix a random $A$ of size $\sqrt{k}$ on which many pairs agree, and define $G$ by plurality vote over sets containing $A$ that agree with a fixed reference set. A combinatorial consistency argument (pairs of sets through $A$ have agreeing values on the remainder) combined with sampling on the Johnson scheme shows that the plurality function explains a $\Omega(\delta)$-fraction of the agreeing sets up to $k^{-c}$-fraction of errors.

## Depends on

- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)
- [Agreement tests for ensembles of local functions](agreement-test.md)

## Sources

- R. Impagliazzo, V. Kabanets, A. Wigderson, "New direct-product testers and 2-query PCPs", SIAM Journal on Computing 41 (2012) 1722-1768.
- I. Dinur, E. Goldenberg, "Locally testing direct product in the low error range", FOCS (2008).
- I. Dinur, D. Steurer, "Direct product testing", CCC (2014), ECCC TR13-179.
