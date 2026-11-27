# Cell-probe lower bounds for problems with almost k-wise independent rows

A static data structure problem whose rows form an almost $k$-wise independent set needs space $S\ge m^{2/t}k^{1-2/t}/(2^{O(w)}\log m)$ for query time $t$ and word length $w$, for every $t$, and small-biased rows give stronger bit-probe bounds.

A static data structure problem is $f:[N]\times[m]\to\{0,1\}$; a cell-probe solution stores row $i$ in $S$ cells of $w$ bits each and answers a query $j\in[m]$ by reading at most $t$ cells, adaptively or not, and outputting $f(i,j)$.

Let the rows of $f$ form the support of an $\eta$-almost $k$-wise independent distribution with $\eta\le(2^{-kw}\cdot m^{-k/\log n})^{O(1)}$, and let $k\ge t\log m$. Every cell-probe data structure for $f$ with space $S$, time $t$ and word length $w$ satisfies

$$
S\ge\frac{m^{2/t}\cdot k^{1-2/t}}{2^{O(w)}\cdot\log m}.
$$

For bit probes ($w=1$):

1. If the rows of $f$ form the support of a $2^{-\Omega(t)}n^{-t}$-biased distribution, every adaptive bit-probe data structure with time $t$ needs space $S\ge\tilde\Omega\left(m^{1/(\frac t2-\frac{t-2}{2(t+2)})}\right)$.
2. Under the same hypothesis, every non-adaptive bit-probe data structure with time $t$ needs space $S\ge\tilde\Omega(m^{2/(t-1)})$.

Here $\tilde\Omega$ hides $\mathrm{polylog}(m)$ factors and constants depending on $t$. The cell-probe bound extends the bound of Korten, Pitassi and Impagliazzo from even $t$ to all $t$ and is almost tight by Siegel's construction with $S=m^{2/t+o(1)}$; in the regime $\log N\ll m$ the previous explicit bound was $\tilde\Omega(m^{1/t})$.

## Expansion

The query algorithm, run on a memory array of $S$ cells, is a circuit from $\Sigma^S$ to $\{0,1\}^m$ whose outputs are $t$-query decision trees, and every row of $f$ must lie in its range. Taking $n=S$ in the remote-point certification theorem, a row drawn from the almost independent distribution is far from the range unless $m$ is below the stated threshold, which rearranges to the space bound. For bit probes, the degree-$t$ Fourier part is split off: the lower-degree part can be strongly refuted with only $m\approx n^{(t-1)/2}$ outputs, and a barely non-trivial bound on the top-degree part suffices. For non-adaptive probes, a non-parity $t$-junta has top-degree Fourier weight below $1-2^{-t}$, and more than $n$ parity outputs would confine the rows to an affine subspace, which a small-biased distribution cannot support; adaptive probes need a further argument in the style of Korten, Pitassi and Impagliazzo.

## Depends on

- [The remote point problem](../../../circuit-complexity/range-avoidance-and-near-maximum-lower-bounds/remote-point-problem.md)

## Proof depends on

- [Certifying remote points for circuits of decision trees](certifying-remote-points-for-decision-tree-circuits.md)

## Sources

- Venkatesan Guruswami, Xin Lyu and Weiqiang Yuan, "Cell-Probe Lower Bounds via Semi-Random CSP Refutation: Simplified and the Odd-Locality Case", *ACM-SIAM Symposium on Discrete Algorithms (SODA)*, 2026, arXiv:2507.22265v1 (Theorems 2, 3 and 4, Section 1.2, Section 5).
