# Pardon's lower bound for the distortion of torus knots

Let $p$ and $q$ be coprime positive
integers, let $T_{p,q}$ be the standard $(p, q)$-torus curve, and let $K$ be a knot with
parametrization $\gamma$. Suppose there are an ambient isotopy $H$ of $\mathbb{R}^3$, with
time-one map $H_1$, and a strictly increasing diffeomorphism $\sigma$ of $\mathbb{R}$ with
$\sigma(t + 2\pi) = \sigma(t) + 2\pi$ for all real $t$, such that
$H_1(\gamma(t)) = T_{p,q}(\sigma(t))$ for every real $t$. Then the distortion of $K$ is at least
$\min(p, q)/160$.

This is the smooth, oriented specialization of Pardon's theorem, which bounds the distortion of
every rectifiable curve in the knot type of the $(p, q)$-torus knot.

## Sources

- John Pardon, 'On the distortion of knots on embedded surfaces', Annals of Mathematics (2) 174 (2011), no. 1, 637-646, Theorem 1.1. https://doi.org/10.4007/annals.2011.174.1.21 Via leanprover/lean-eval@38361be, problem `pardon_torus_knot_distortion`.
