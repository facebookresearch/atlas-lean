# Circuit samplers and output distributions

A Boolean circuit $C$ with $n$ inputs and $m$ outputs is a *sampler*: its *output distribution* $D_C$ is the distribution of $C(r)\in\{0,1\}^m$ for $r$ uniform in $\{0,1\}^n$, that is $D_C(y)=2^{-n}\,|\{r: C(r)=y\}|$. Pairs of samplers are compared by the statistical (total variation) distance $\Delta(D_{C_0},D_{C_1})=\tfrac12\sum_y |D_{C_0}(y)-D_{C_1}(y)|$.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)

## Sources

- Amit Sahai, Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM, 2003.
