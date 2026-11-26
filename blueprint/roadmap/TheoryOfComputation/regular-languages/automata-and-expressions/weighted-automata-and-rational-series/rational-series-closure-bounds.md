# Closure of rational series with dimension bounds

If $f\in\mathrm{Rat}_{\le m}$ and $g\in\mathrm{Rat}_{\le n}$ then $f+g\in\mathrm{Rat}_{\le m+n}$, the Cauchy product $f\cdot g\in\mathrm{Rat}_{\le m+n}$, scalar multiples $cf\in\mathrm{Rat}_{\le m}$, and (when $f(\varepsilon)=0$) the star $f^{*}=\sum_{k\ge0}f^{k}\in\mathrm{Rat}_{\le m+1}$; each single-letter series lies in $\mathrm{Rat}_{\le2}$. Every rational series has a normal-form representation with a single initial and a single final state agreeing on non-empty words, and padding words with a trailing idle letter raises the dimension by at most one.

## Proof sketch

Block-diagonal sum of representations for $f+g$; for the product, a block upper-triangular representation whose off-diagonal block is $\rho_f\lambda_g$; for the star, add a state feeding the final vector back to the initial vector.

## Depends on

- [Linear representations and rational series of bounded dimension](rational-series-linear-representations.md)

## Sources

- Jean Berstel and Christophe Reutenauer, "Noncommutative Rational Series with Applications", Cambridge University Press, 2011.
- Marcel-Paul Schützenberger, "On the Definition of a Family of Automata", Information and Control 4, 1961.
