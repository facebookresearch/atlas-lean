# Inverting one-way functions yields average-case conditional coding for pK

If infinitely-often one-way functions do not exist, then average-case conditional coding (in its high-probability form) holds for every polynomial-time samplable family $\{D_n\}$ of pairs: for every polynomial $q$ there is a polynomial $p$ such that for all large $n$, with probability at least $1-1/q(n)$ over $(x,y)\sim D_n$,

$$
\mathrm{pK}^{p(n)}(x\mid y)\le\log\frac{1}{D_n(x\mid y)}+\log p(n).
$$

## Proof sketch

Without one-way functions one can efficiently approximate, up to a constant factor and on most pairs, the probability $D_n(x\mid y)$ (Impagliazzo–Levin style approximate counting of samplable probabilities obtained by inverting a suitable function). Define the efficiently computable $f(r_D,r_B,w)=(H_w(x),y,p,r_B,w)$, where $(x,y)$ is sampled with seed $r_D$, $p$ is the largest power of two below the estimate of $D_n(x\mid y)$ computed with coins $r_B$, and $H_w$ is a pairwise-independent hash taken from $w$ with output length $\log(1/p)+O(\log n)$, which isolates $x$ among the at most $O(1/p)$ strings $a$ with $D_n(a\mid y)\ge p$. An inverter for $f$ recovers $x$ from $(H_w(x),y,p,r_B,w)$; treating $w$ and $r_B$ as the public random string, the description consists of $H_w(x)$ and $p$, of total length $\log(1/D_n(x\mid y))+O(\log n)$, decodable in polynomial time.

## Depends on

- [Average-case symmetry of information, conditional coding and language compression over samplable pairs](average-case-kolmogorov-principles-over-samplable-pairs.md)
- [One-way functions exist](../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)
- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [Pairwise-independent hashing by affine maps over GF(2)](../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Stockmeyer: approximate counting of #P functions in BPP^NP](../../counting-complexity/stockmeyer-approximate-counting.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
