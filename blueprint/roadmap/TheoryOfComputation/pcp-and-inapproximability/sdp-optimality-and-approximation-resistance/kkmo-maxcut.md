# Khot–Kindler–Mossel–O'Donnell: Goemans–Williamson is optimal for Max-Cut under UGC

Assume the Unique Games Conjecture. Then for every $\varepsilon > 0$ it is NP-hard to approximate Max-Cut within a factor $\alpha_{GW} + \varepsilon$, where

$$
\alpha_{GW} = \min_{0 < \theta \le \pi} \frac{2}{\pi} \cdot \frac{\theta}{1 - \cos\theta} \approx 0.87856
$$

is the Goemans-Williamson constant. More precisely, for every $\rho \in (-1, 0)$ it is UG-hard to distinguish graphs with maximum cut at least $\frac{1 - \rho}{2} - \varepsilon$ from graphs with maximum cut at most $\frac{\arccos \rho}{\pi} + \varepsilon$.

## Proof sketch

Use the $\rho$-correlated noise dictatorship test: on input $F : \{-1,1\}^R \to \{-1,1\}$, pick $x$ uniform and $y$ that is $\rho$-correlated with $x$, and accept iff $F(x) \ne F(y)$. Dictators pass with probability $\frac{1 - \rho}{2}$; by the Majority Is Stablest theorem, functions with low influences pass with probability at most $\frac{\arccos\rho}{\pi} + o(1)$. Composing with Unique Games and optimizing $\rho$ gives the ratio $\alpha_{GW}$.

## Depends on

- [The Goemans–Williamson constant](../../../ComputerScience/approximation-algorithms/goemans-williamson-max-cut-algorithm/gw-constant.md)
- [MAX-CUT as an optimization problem](../inapproximability-of-max-cut/max-cut.md)
- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)

## Proof depends on

- [Dictatorship tests compose with Unique Games to give hardness](dictatorship-to-ug-hardness.md)
- [Majority Is Stablest](../../../Combinatorics/boolean-functions/structure-theorems-for-boolean-functions/majority-is-stablest.md)

## Sources

- S. Khot, G. Kindler, E. Mossel, R. O'Donnell, "Optimal inapproximability results for MAX-CUT and other 2-variable CSPs?", SIAM Journal on Computing 37 (2007) 319-357.
- E. Mossel, R. O'Donnell, K. Oleszkiewicz, "Noise stability of functions with low influences: invariance and optimality", Annals of Mathematics 171 (2010) 295-341.
