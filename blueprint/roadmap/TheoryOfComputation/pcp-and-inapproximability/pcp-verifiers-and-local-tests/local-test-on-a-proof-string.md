# Local test on a proof string

Let $P$ be a finite set of proof positions, $\Gamma$ a finite alphabet, $R$ a finite nonempty set of random strings and $Q$ a finite nonempty set of query indices. A *local test* $T$ consists of a query map $\mathrm{query} : R \times Q \to P$ and a decision predicate $D_r : \Gamma^Q \to \{0,1\}$ for every $r \in R$. For a proof $\pi : P \to \Gamma$, the test *passes on* $r$ when $D_r\big((\pi(\mathrm{query}(r,i)))_{i \in Q}\big) = 1$, and its *acceptance probability* is

$$\mathrm{acc}_T(\pi) = \Pr_{r \in R}\big[T \text{ passes on } r\big],$$

with $r$ uniform. The test makes $|Q|$ queries and uses $\log_2 |R|$ random bits. A PCP verifier on a fixed input is a local test; the BLR linearity test is the case $\Gamma = \{0,1\}$, $|Q| = 3$.

## Depends on

- [Blum–Luby–Rubinfeld linearity test](../blum-luby-rubinfeld-linearity-test/blr-test.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
