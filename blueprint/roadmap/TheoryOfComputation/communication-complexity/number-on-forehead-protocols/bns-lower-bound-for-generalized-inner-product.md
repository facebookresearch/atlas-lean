# Babai–Nisan–Szegedy lower bound for the generalized inner product

For $k \ge 2$, the *generalized inner product* of $k$ strings $x_1, \dots, x_k \in \{0,1\}^n$ is $\mathrm{GIP}_{k,n}(x) = \bigoplus_{r=1}^n \bigwedge_{i=1}^k x_{i,r}$; for $k = 2$ it is the inner product modulo two. Its uniform cube expectation is $\big(1 - 2^{1-k}\big)^n$, hence, by the cube bound, $\mathrm{disc}^k(\mathrm{GIP}_{k,n}) \le (1 - 2^{1-k})^{n/2^k} \le \exp(-2n / 4^{k})$, and every public-coin NOF protocol computing $\mathrm{GIP}_{k,n}$ with error at most $1/3$ has cost $\Omega(n / 4^k)$.

## Proof sketch

Over the corners of the cube spanned by $a$ and $b$ the GIP values add up (in $\mathbb{F}_2$) to $\bigoplus_r \bigwedge_i (a_{i,r} \oplus b_{i,r})$ by distributivity in the Boolean ring, so the cube expectation is the bias of an AND of $k$ uniform bits, raised to the $n$th power, $(1 - 2^{1-k})^n$. The cube bound then gives the discrepancy.

## Depends on

- [Multiparty discrepancy](multiparty-discrepancy.md)

## Proof depends on

- [The BNS–Chung cube bound on multiparty discrepancy](bns-chung-cube-bound.md)

## Sources

- L. Babai, N. Nisan and M. Szegedy, "Multiparty Protocols, Pseudorandom Generators for Logspace, and Time-Space Trade-offs", Journal of Computer and System Sciences 45(2), 1992.
- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
