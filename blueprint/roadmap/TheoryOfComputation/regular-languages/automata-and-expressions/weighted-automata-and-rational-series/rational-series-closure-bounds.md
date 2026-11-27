# Closure of rational series with dimension bounds

If $f\in\mathrm{Rat}_{\le m}$ and $g\in\mathrm{Rat}_{\le n}$ then $f+g\in\mathrm{Rat}_{\le m+n}$, the Cauchy product $f\cdot g\in\mathrm{Rat}_{\le m+n}$, scalar multiples $cf\in\mathrm{Rat}_{\le m}$, and (when $f(\varepsilon)=0$) the star $f^{*}=\sum_{k\ge0}f^{k}\in\mathrm{Rat}_{\le m+1}$; each single-letter series lies in $\mathrm{Rat}_{\le2}$. Every rational series $f \in \mathrm{Rat}_{\le m}$ admits a representation of dimension at most $m + 2$ with a single initial basis vector $e_1$ and a single final basis vector $e_{m+2}$ agreeing with $f$ on all non-empty words.

## Proof sketch

Block-diagonal sum of representations for $f+g$; for the product, the block upper-triangular representation with $\mu(a)=\begin{pmatrix}\mu_f(a)&\rho_f\lambda_g\mu_g(a)\\0&\mu_g(a)\end{pmatrix}$, initial vector $(\lambda_f,0)$ and final vector $(\rho_f\lambda_g\rho_g;\rho_g)$, which sums $f(u)g(v)$ over all factorizations $w=uv$; for the star, add a state feeding the final vector back to the initial vector.

## Depends on

- [Rational series of bounded dimension](rational-series-linear-representations.md)

## Sources

- Jean Berstel and Christophe Reutenauer, "Noncommutative Rational Series with Applications", Encyclopedia of Mathematics and its Applications 137, Cambridge University Press, 2011, Chapter 1 (closure of recognizable series under sum, Cauchy product and star of proper series, with the standard constructions).
- Marcel-Paul Schützenberger, "On the Definition of a Family of Automata", Information and Control 4(2–3), 245–270, 1961.
