# Duality for rK in the quasi-polynomial regime: without one-way functions rK^quasipoly(x|y) ≈ K(x|y) on samplable pairs

Call $\exp(\log^{c}n)$ for a constant $c$ a quasi-polynomial. The following are equivalent:

1. There is no infinitely-often polynomial-time computable one-way function secure against quasi-polynomial-time randomized algorithms.
2. For every polynomial-time samplable family $\{D_n\}$ of pairs and every quasi-polynomial $q$ there is a quasi-polynomial $p$ such that for every computable $t\ge p$, with probability at least $1-1/q(n)$ over $(x,y)\sim D_n$: $\mathrm{rK}^{t(n)}(x,y)\ge \mathrm{rK}^{t(n)}(x\mid y)+\mathrm{rK}^{t(n)}(y)-\log t(n)$.
3. Item 2 holds with an efficient encoder: a quasi-polynomial-time randomized algorithm that, given $(x,y)$, outputs (with the same probability) a randomized program of length at most $\mathrm{rK}^{t(n)}(x,y)-\mathrm{rK}^{t(n)}(y)+\log t(n)$ that maps $y$ to $x$ in time $p(n)$.
4. For every such family and quasi-polynomial $q$ there is a quasi-polynomial $p$ with $\Pr_{(x,y)\sim D_n}\bigl[\mathrm{rK}^{p(n)}(x\mid y)\le K(x\mid y)+\log p(n)\bigr]\ge 1-1/q(n)$.

Item 4 says that, absent such one-way functions, randomized quasi-polynomial-time-bounded complexity and time-unbounded Kolmogorov complexity essentially coincide on samplable pairs.

## Proof sketch

The proof follows the same template as the $\mathrm{pK}$ duality, but the encoder must now produce a private-coin program, so the hashing description must be turned into a decoder that regenerates the isolating hash itself; inverting quasi-polynomially secure functions provides the needed search, which is why the equivalence lives in the quasi-polynomial regime. Item 4 follows because the inverter can efficiently realize the time-unbounded coding bound $K(x\mid y)\approx\log(1/D_n(x\mid y))$ on samples.

## Depends on

- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)
- [One-way functions exist](../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)

## Proof depends on

- [Hirahara–Ilango–Lu–Nanashima–Oliveira: one-way functions exist iff probabilistic time-bounded SoI fails on average](hilno-owf-iff-average-case-soi-fails.md)
- [Inverting one-way functions yields average-case conditional coding for pK](inverting-owf-gives-average-case-conditional-coding.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
