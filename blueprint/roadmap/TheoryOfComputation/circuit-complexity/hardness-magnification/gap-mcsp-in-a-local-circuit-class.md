# Gap-MCSP is computable by local oracle circuits

For every constructive $s(n) \le 2^n / \mathrm{poly}(n)$ at input length $N = 2^n$, $\mathrm{Gap\text{-}MCSP}[s_1, s_2]$ with $s_1 = s/(10n)$ and $s_2 = s$ (the gap of Oliveira, Pich and Santhanam 2019, whose Theorem 4 and its proof take $s = 2^{\beta n}$) is computed by oracle circuits with one fixed oracle (the anti-checker oracle), $N \cdot \mathrm{poly}(s)$ gates, at most $N \cdot \mathrm{poly}(s)$ oracle gates, each of fan-in at most $\mathrm{poly}(s)$, and at most $\mathrm{poly}(s)$ oracle gates on any path (Oliveira, Pich and Santhanam 2019, as stated by Chen et al. 2020, Appendix A.2). Hence $\mathrm{Gap\text{-}MCSP}[s_1, s_2]$ lies in $[N \mathrm{poly}(s), \mathrm{poly}(s), \mathrm{poly}(s)]\text{-}\mathrm{Circuit}[N \mathrm{poly}(s)]$, so lower-bound techniques that apply to such local circuits cannot prove the hypotheses of the magnification theorems (the locality barrier).

## Proof sketch

Implement the anti-checker generator as an oracle circuit: blocks of the truth table are hashed and queried to an oracle that returns small refuting sets; a final oracle gate checks the existence of a small circuit consistent with the sampled inputs. All oracle queries have length polynomial in $s = s_2$.

## Depends on

- [Oracle circuits and local circuit classes](oracle-circuits-and-local-circuit-classes.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../minimum-circuit-size-problem/minimum-circuit-size-problem.md)

## Proof depends on

- [Small anti-checkers exist for functions without small circuits](small-anti-checkers-exist.md)

## Sources

- L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020.
- I. C. Oliveira, J. Pich and R. Santhanam, "Hardness Magnification near State-Of-The-Art Lower Bounds", Computational Complexity Conference (CCC) 2019.
