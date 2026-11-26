# Gap-MCSP is computable by local oracle circuits

Whenever $n s_1 + 2 + 2n(n + 2) \le s_2$ at input length $N = 2^n$, a single oracle circuit with a fixed oracle (the anti-checker oracle) accepts the yes-instances and rejects the no-instances of $\mathrm{Gap\text{-}MCSP}[s_1, s_2]$, with at most $5000\, N s_2^5$ gates, at most $610\, N s_2^4 + 1$ oracle gates, oracle fan-in at most $5000\, s_2^5$, and at most $610\, s_2^4 + 1$ oracle gates on any path. Hence Gap-MCSP lies in $[N \mathrm{poly}(s), \mathrm{poly}(s), \mathrm{poly}(s)]\text{-}\mathrm{Circuit}[N \mathrm{poly}(s)]$, so lower-bound techniques that apply to such local circuits cannot prove the hypotheses of the magnification theorems (the locality barrier).

## Proof sketch

Implement the anti-checker generator as an oracle circuit: blocks of the truth table are hashed and queried to an oracle that returns small refuting sets; a final oracle gate checks the existence of a small circuit consistent with the sampled inputs. All oracle queries have length polynomial in $s_2$.

## Depends on

- [Oracle circuits and local circuit classes](oracle-circuits-and-local-circuit-classes.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../minimum-circuit-size-problem/minimum-circuit-size-problem.md)

## Proof depends on

- [Small anti-checkers exist for functions without small circuits](small-anti-checkers-exist.md)

## Sources

- L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020.
- I. C. Oliveira, J. Pich and R. Santhanam, "Hardness Magnification near State-Of-The-Art Lower Bounds", Computational Complexity Conference (CCC) 2019.
