# Gap(K^A vs K) is easy if NP^A is easy on average

For every oracle $A$, if $\mathrm{DistNP}^A\subseteq\mathrm{AvgP}$ then one can distinguish strings with small $A$-oracle time-bounded complexity from strings with large oracle-free complexity in polynomial time. For $A=\mathrm{SAT}$ the problem is conjectured to be non-disjoint, so its solvability would itself be surprising.

For an oracle $A$ and $\tau:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$, $\mathrm{Gap}_\tau(K^A\text{ vs }K)$ is the promise problem

$$
\Pi_{\mathrm{Yes}}=\{(x,1^s,1^t) : K^{t,A}(x)\le s\},\qquad \Pi_{\mathrm{No}}=\{(x,1^s,1^t) : K^{\tau(|x|,t)}(x)>s+\log\tau(|x|,t)\},
$$

and $\mathrm{Gap}(K^A\text{ vs }K)\in\mathrm{P}$ means $\mathrm{Gap}_\tau(K^A\text{ vs }K)\in\mathrm{P}$ for some polynomial $\tau$.

1. For every oracle $A$: if $\mathrm{DistNP}^A\subseteq\mathrm{AvgP}$, then $\mathrm{Gap}(K^A\text{ vs }K)\in\mathrm{P}$. With $A=\varnothing$ this approximates $K^t(x)$ within additive error $\log\tau(|x|,t)$, improving the $\widetilde{O}(\sqrt{s})$ error of the earlier non-black-box reduction.
2. If $\mathrm{DistPH}\subseteq\mathrm{AvgP}$, there is a polynomial $\tau$ with $K^{\tau(|x|,t)}(x)\le K^{t,\mathrm{SAT}}(x)+\log\tau(|x|,t)$ for all $x$ and $t$.
3. If $\mathrm{E}^{\mathrm{NP}}\ne\mathrm{E}$, then for some polynomial $\tau_0$ and every polynomial $\tau$ there are infinitely many $x$ with $K^{t,\mathrm{SAT}}(x)=O(\log|x|)$ and $K^{\tau(|x|)}(x)>\log\tau(|x|)$, where $t=\tau_0(|x|)$; so $\mathrm{Gap}(K^{\mathrm{SAT}}\text{ vs }K)$ is non-disjoint.

Hence a super-polynomial lower bound for $\mathrm{Gap}(K^{\mathrm{SAT}}\text{ vs }K)$, a problem believed to have no algorithm at all, would prove $\mathrm{DistPH}\not\subseteq\mathrm{AvgP}$.

## Expansion

The proof views a black-box pseudorandom generator construction meta-computationally. Two sources of approximation error in the earlier reduction are removed: fixing random coins, via the Buhrman–Fortnow–Pavan generator available when $\mathrm{DistNP}\subseteq\mathrm{AvgP}$, and the advice complexity of the construction, by using the $k$-wise direct product generator, whose reconstruction needs little advice. An average-case algorithm relative to $A$ distinguishes the generator's outputs on strings of small $K^{t,A}$ complexity from random strings, and reconstruction turns this into short oracle-free descriptions. For item 3, take $L\in\mathrm{E}^{\mathrm{NP}}\setminus\mathrm{E}/O(n)$ and let $x$ be the truth table of $L$ at length $n$.

## Depends on

- [The promise problem GapMINKT](gap-minkt-promise-problem.md)
- [Easy on average](../../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/avg-easy.md)

## Proof depends on

- [Hirahara: errorless average-case easiness of MINKT yields worst-case additive approximation of K^t](../../probabilistic-kolmogorov-and-symmetry-of-information/hirahara-non-black-box-worst-to-average-minkt.md)

## Sources

- Shuichi Hirahara, "Non-Disjoint Promise Problems from Meta-Computational View of Pseudorandom Generator Constructions", *35th Computational Complexity Conference (CCC 2020)*, LIPIcs 169, 2020, [doi:10.4230/LIPIcs.CCC.2020.20](https://doi.org/10.4230/LIPIcs.CCC.2020.20) (Definition 3, Theorem 4, Corollary 5, Definition 17, Proposition 24).
