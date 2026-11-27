# DistNP ⊆ HeurBPP iff independent average-case conditional coding and language compression hold for pK

Recall that $\mathsf{DistNP}\subseteq\mathsf{HeurBPP}$ means that for every $L\in\mathsf{NP}$ and polynomial-time samplable $\{S_n\}$ there is a probabilistic polynomial-time heuristic that, given $1/\delta$, errs on at most a $\delta$ fraction of $S_n$. The following are equivalent:

1. $\mathsf{DistNP}\subseteq\mathsf{HeurBPP}$.
2. Independent average-case conditional coding: for all polynomial-time samplable families $\{D_n\}$ over pairs and $\{C_n\}$ over the second marginal's support, and every polynomial $q$, there is a polynomial $p$ with $\Pr_{y\sim C_n,\,x\sim D_n(\cdot\mid y)}\bigl[\mathrm{pK}^{p(n)}(x\mid y)\le\log\frac1{D_n(x\mid y)}+\log p(n)\bigr]\ge1-1/q(n)$.
3. Independent average-case language compression, defined analogously with $\log|L_y|$ in place of $\log(1/D_n(x\mid y))$.

Thus the gap between inverting one-way functions and solving $\mathsf{NP}$ on average is exactly the gap between sampling $y$ jointly with $x$ and sampling $y$ from an arbitrary independent samplable distribution.

## Proof sketch

From average-case easiness of NP one obtains conditional extrapolation: given $y$ from an arbitrary samplable source, one can estimate $D_n(x\mid y)$ and invert the sampler conditioned on $y$, which, together with hashing, gives the coding bound as in the one-way-function case. Conversely, coding and compression with respect to independently chosen $y$ let the universal sampler find witnesses for a distributional NP problem: the instance plays the role of $y$ and the witness set plays the role of $L_y$.

## Depends on

- [Average-case symmetry of information, conditional coding and language compression over samplable pairs](average-case-kolmogorov-principles-over-samplable-pairs.md)
- [Heuristica](../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/heuristica.md)
- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [Inverting one-way functions yields average-case conditional coding for pK](inverting-owf-gives-average-case-conditional-coding.md)
- [Average-case language compression inverts every polynomial-time function via the universal sampler](language-compression-inverts-functions.md)
- [The universal time-bounded sampler hits every x with probability about 2^{−pK^t(x|y)}](universal-time-bounded-sampler-and-pkt.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
