# ETH lower bound for bipartite permutation independent set

In the $2k\times 2k$ Bipartite Permutation Independent Set problem, the input is a graph $G$ on the vertex set $[2k]\times[2k]$ in which every edge joins the upper-left quadrant $I_1=\{(i,j): i,j\le k\}$ to the lower-right quadrant $I_2=\{(i,j): i,j\ge k+1\}$, the parameter is $k$, and the question is whether there is a permutation $\rho$ of $[2k]$ such that $\{(1,\rho(1)),\dots,(2k,\rho(2k))\}\subseteq I_1\cup I_2$ is an independent set of $G$ (so $\rho$ maps $[k]$ onto $[k]$ and $\{k+1,\dots,2k\}$ onto itself). Assuming ETH, this problem cannot be solved in time $2^{o(k\log k)}$.

## Proof sketch

Reduce from $k\times k$ Permutation Independent Set (choose one vertex $(i,\delta(i))$ per row of a graph on $[k]\times[k]$, with $\delta$ a permutation), which has no $2^{o(k\log k)}$ algorithm under ETH (Lokshtanov–Marx–Saurabh, via $k\times k$ Permutation Clique and complementation). Given an instance $I$, join $(i,j)$ to $(i+k,j'+k)$ for all $i$ and all $j\ne j'$, and join $(i_1,j_1)$ to $(i_2+k,j_2+k)$ whenever $(i_1,j_1)(i_2,j_2)$ is an edge of $I$. The first family of edges forces $\rho(i+k)=\rho(i)+k$ in every solution, so solutions of the new instance are exactly two shifted copies of solutions of $I$; the parameter only doubles.

## Depends on

- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Sources

- Daniel Lokshtanov, Dániel Marx and Saket Saurabh, "Slightly Superexponential Parameterized Problems", SIAM Journal on Computing 47(3), 2018, Section 2.2, Theorem 2.11.
- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Theorems 14.13 and 14.14 (the $k\times k$ Permutation Clique lower bound).
- Rahul Ilango, "Approaching MCSP from Above and Below: Hardness for a Conditional Variant and AC^0[p]", 11th Innovations in Theoretical Computer Science Conference (ITCS 2020), 2020.
