# Average-case conditional coding implies average-case symmetry of information and language compression

For every polynomial-time samplable family $\{D_n\}$ of pairs, strong average-case conditional coding for $\{D_n\}$ and for its second marginal implies strong average-case symmetry of information for $\mathrm{pK}$ and strong average-case language compression for $\{D_n\}$. For the weak versions (success probability at least $1/q(n)$ for some polynomial $q$), weak conditional coding for $\{D_n\}$ implies weak language compression for $\{D_n\}$; for symmetry of information the direct argument gives only the converse (weak symmetry of information implies weak conditional coding), and the forward implication holds only globally: if weak conditional coding holds for every samplable family, then weak symmetry of information holds for every samplable family, through the equivalence of all these statements with the non-existence of infinitely-often one-way functions.

## Proof sketch

For SoI, apply coding to the pair distribution and to its marginal $D'_n$ on $y$: with high probability $\mathrm{pK}^{t}(x\mid y)\le\log\frac{1}{D_n(x\mid y)}+O(\log t)$ and $\mathrm{pK}^{t}(y)\le\log\frac{1}{D'_n(y)}+O(\log t)$, while a counting (incompressibility) bound shows that a sample $(x,y)\sim D_n$ satisfies $\mathrm{pK}^t(x,y)\ge\log\frac{1}{D_n(x,y)}-O(\log t)$ with high probability; the chain rule $D_n(x,y)=D'_n(y)D_n(x\mid y)$ closes the inequality. For language compression, combine coding with the bound $K(x\mid y)\ge\log\frac1{D_n(x\mid y)}-O(\log n)$ that holds with high probability, which forces $D_n(x\mid y)\gtrsim 1/|L_y|$ on most samples landing in $L_y$.

## Depends on

- [Average-case symmetry of information, conditional coding and language compression over samplable pairs](average-case-kolmogorov-principles-over-samplable-pairs.md)
- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [Sandwich bounds: K(x) − O(log t) ≤ pK^t(x) ≤ rK^t(x), K^t(x) up to constants and time overhead](pkt-sandwich-between-kolmogorov-and-time-bounded.md)
- [Few strings have small complexity](../incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
