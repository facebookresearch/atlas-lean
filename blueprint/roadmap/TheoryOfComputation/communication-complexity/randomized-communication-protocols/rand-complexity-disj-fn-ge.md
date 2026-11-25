# Randomized communication complexity of disjointness

For every fixed $0 \le \varepsilon < 1/2$ there is $c > 0$ such that, for every $n$, every
public-coin protocol that decides whether two subsets of $\{1, \dots, n\}$ intersect, with error at
most $\varepsilon$ on every input, has worst-case cost at least $cn$:
$R_\varepsilon(\mathrm{DIS}_n) \ge cn$.

This is the linear lower bound of Kalyanasundaram and Schnitger and of Razborov, as quoted by Alon,
Matias and Szegedy: "for any fixed $\varepsilon < 1/2$, $C_\varepsilon(\mathrm{DIS}_n) \ge \Omega(n)$",
and Razborov "exhibited a simple measure $\mu$ … and showed that for this measure
$D_\varepsilon(\mathrm{DIS}_n \mid \mu) \ge \Omega(n)$". The public-coin form follows from
Razborov's distributional bound. A public-coin protocol with error at most $\varepsilon'$ on every
input has $\mu$-error at most $\varepsilon'$, so its cost is at least the distributional complexity
([distributional complexity is at most randomized complexity](dist-complexity-le-rand-complexity.md)),
which is $\Omega(n)$ at Razborov's fixed small error $\varepsilon'$. A protocol with error
$\varepsilon < 1/2$ reaches error $\varepsilon'$ by taking the majority answer of $O_\varepsilon(1)$
independent runs, which multiplies the cost by a constant depending only on $\varepsilon$.

## Background

- [Distributional complexity is at most randomized complexity](dist-complexity-le-rand-complexity.md): the route from Razborov's distributional bound to a public-coin bound.
- [Yao's minimax principle for communication complexity](rand-complexity-eq-i-sup-dist-complexity.md): the equality behind distributional lower-bound proofs.

## Sources

- B. Kalyanasundaram and G. Schnitger, "The probabilistic communication complexity of set intersection", *SIAM J. Discrete Math.* 5 (1992) 545–557.
- A. A. Razborov, "On the distributional complexity of disjointness", *Theoret. Comput. Sci.* 106 (1992) 385–390.
- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *J. Comput. System Sci.* 58 (1999) 137–147, Section 3, where the two results above are quoted.
