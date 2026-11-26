# Consistent measurements are close in the state

Let $P,Q$ be measurements with the same finite outcome set in a star-ordered algebra, with $P_a$ commuting with $Q_b$ for all $a,b$, and let $\varphi$ be a state. Then

$$
\sum_a\|P_a-Q_a\|_\varphi^2\le 2\Big(1-\sum_a\operatorname{Re}\varphi(P_aQ_a)\Big),
$$

with equality when both are projective. Hence agreement at least $1-\varepsilon$ gives $\sum_a\|P_a-Q_a\|_\varphi^2\le 2\varepsilon$, and for families agreement at least $1-\varepsilon$ on every question gives family closeness $\sqrt{2\varepsilon}$.

## Proof sketch

An effect satisfies $E^2\le E$, so $\|P_a-Q_a\|_\varphi^2 = \varphi(P_a^2)+\varphi(Q_a^2)-2\operatorname{Re}\varphi(P_aQ_a)\le\varphi(P_a)+\varphi(Q_a)-2\operatorname{Re}\varphi(P_aQ_a)$. Summing over $a$ and using $\sum_aP_a = \sum_aQ_a = 1$ gives $2-2\cdot$agreement.

## Depends on

- [Measurements, agreement and character observables in a star-ordered algebra](algebraic-measurements-and-agreement.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
