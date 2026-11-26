# NP ⊆ BPP iff worst-case conditional coding iff worst-case language compression for pK

The following are equivalent:

1. $\mathsf{NP}\subseteq\mathsf{BPP}$.
2. Worst-case conditional coding: for every polynomial-time samplable family $\{D_n\}$ over $\{0,1\}^n\times\{0,1\}^n$ there is a polynomial $p$ such that for all large $n$ and all $(x,y)$ in the support of $D_n$, $\mathrm{pK}^{p(n)}(x\mid y)\le\log\frac{1}{D_n(x\mid y)}+\log p(n)$.
3. Worst-case language compression: for every polynomial-time computable $L$ there is a polynomial $p$ such that for all large $n$ and all $x,y\in\{0,1\}^n$, $x\in L_y\Rightarrow\mathrm{pK}^{p(n)}(x\mid y)\le\log|L_y|+\log p(n)$.

The equivalence persists when $\mathrm{pK}$ is replaced by $\mathrm{rK}$ in items 2 and 3.

## Proof sketch

If $\mathsf{NP}\subseteq\mathsf{BPP}$, approximate counting and uniform sampling of NP witnesses are in $\mathsf{BPP}$, so $D_n(x\mid y)$ can be estimated and $x$ isolated by a hash for every pair, giving conditional coding, which in turn implies compression for polynomial-time $L$ via the uniform distribution on $L_y$. Conversely, worst-case compression of a polynomial-time witness relation lets the universal sampler output a witness for every satisfiable instance with probability $1/\mathrm{poly}$, so search-NP and hence NP is in $\mathsf{BPP}$.

## Depends on

- [Average-case symmetry of information, conditional coding and language compression over samplable pairs](average-case-kolmogorov-principles-over-samplable-pairs.md)
- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

- [One-way functions imply P ≠ NP](../../pseudorandomness-and-one-way-functions/owf-implies-p-ne-np.md)
- [The universal time-bounded sampler hits every x with probability about 2^{−pK^t(x|y)}](universal-time-bounded-sampler-and-pkt.md)
- [Stockmeyer: approximate counting of #P functions in BPP^NP](../../counting-complexity/stockmeyer-approximate-counting.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
