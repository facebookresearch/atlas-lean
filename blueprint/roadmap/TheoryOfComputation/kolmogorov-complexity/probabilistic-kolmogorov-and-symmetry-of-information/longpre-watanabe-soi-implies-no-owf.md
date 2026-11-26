# Longpré–Mocas and Longpré–Watanabe: polynomial-time symmetry of information rules out one-way functions

If polynomial-time symmetry of information holds for $K^t$, then one-way functions do not exist: for every polynomial-time computable $f:\{0,1\}^*\to\{0,1\}^*$ there is a polynomial-time algorithm that inverts $f$ on a non-negligible fraction of inputs $x\sim\{0,1\}^n$ for infinitely many $n$ (in fact for all large $n$). The same argument applied to $\mathrm{pK}^t$ rules out one-way functions secure against probabilistic polynomial-time adversaries. Longpré and Watanabe further show that polynomial-time SoI holds if $\mathsf{P}=\mathsf{NP}$, and Longpré and Mocas asked whether a converse holds; that converse is settled on average by the Hirahara–Ilango–Lu–Nanashima–Oliveira duality.

## Proof sketch

For injective $f$ and uniformly random $x\in\{0,1\}^n$: $x$ determines $f(x)$ efficiently, so $K^t(x,f(x))\le n+O(\log n)$, while counting and injectivity give $K^{p(t)}(f(x))\ge K(f(x))\ge n-O(\log n)$ for most $x$. SoI then forces $K^{p(t)}(x\mid f(x))\le O(\log n)$, so enumerating all programs of length $O(\log n)$ on input $f(x)$ for $p(t)$ steps and checking the output against $f$ inverts $f$ in polynomial time. General $f$ are reduced to the almost-injective case by appending a pairwise-independent hash of $x$ whose output length guesses $\log|f^{-1}(f(x))|$.

## Depends on

- [Polynomial-time symmetry of information hypothesis for K^t and pK^t](polynomial-time-symmetry-of-information-hypothesis.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [One-way functions exist](../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)
- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [Few strings have small complexity](../incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Luc Longpré and Sarah Mocas, "Symmetry of information and one-way functions", Information Processing Letters (1993).
- Luc Longpré and Osamu Watanabe, "On symmetry of information and polynomial time invertibility", Information and Computation 121(1) (1995).
- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
