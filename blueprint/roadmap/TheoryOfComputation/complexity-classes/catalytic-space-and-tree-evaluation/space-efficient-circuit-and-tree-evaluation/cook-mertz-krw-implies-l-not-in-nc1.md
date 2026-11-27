# Cook–Mertz: the KRW conjecture implies L ⊄ NC^1

If the KRW conjecture holds, then $\mathsf{L}\not\subseteq\mathsf{NC}^1$, i.e. some logspace language requires formulas of super-logarithmic depth. The implication is robust: any form of the conjecture implying that Tree Evaluation requires formula depth $\omega(\log n)$ suffices; the strongest, most studied form implies that $\mathsf{L}$ requires formula depth $\Omega(\log^2 n/\log\log n)$, close to the upper bound $O(\log^2 n)$ from $\mathsf{L}\subseteq\mathsf{NC}^2$. Under KRW this gives a superpolynomial separation between formulas and uniform branching programs.

## Proof sketch

Recall that Cook–Mertz evaluate $\mathrm{TreeEval}$ in space $O(\log n\cdot\log\log n)$, and more finely in space that is logarithmic for suitable parameter regimes of $k$ and $h$. Choosing parameters (and padding) so that the Tree Evaluation instances are logspace computable while the KRW-derived depth lower bound for iterated composition remains super-logarithmic places a language in $\mathsf{L}$ outside $\mathsf{NC}^1$. With the earlier $O(\log^2 n/\log\log n)$ space bound both hypotheses could hold simultaneously, so this conclusion needs the newer algorithm.

## Depends on

- [The Karchmer–Raz–Wigderson composition conjecture for formula depth](karchmer-raz-wigderson-conjecture.md)
- [Deterministic logarithmic space](../../time-and-space-complexity-classes/log-space.md)

## Proof depends on

- [Cook–Mertz: Tree Evaluation in space O(h log k / log h + h), i.e. O(log^2 n / log log n)](cook-mertz-treeeval-space-log-squared-over-loglog.md)
- [NC^1 is contained in L](../../../circuit-complexity/parallel-complexity-class-nc/nc1-subset-logspace.md)

## Sources

- James Cook and Ian Mertz, "Tree Evaluation Is in Space O(log n · log log n)", STOC (2024), ECCC TR23-174.
