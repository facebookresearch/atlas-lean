# Lutz's measure conservation: E does not have measure zero in E

No p-martingale succeeds on every language in $\mathsf{E}$; in fact for every p-martingale $d$ and every cylinder $C_w=\{A : w\sqsubseteq A\}$ there is $A\in\mathsf{E}\cap C_w$ on which $d$ does not succeed. Hence $\mathsf{E}$ does not have measure zero in $\mathsf{E}$, while for every $k$ the class $\mathsf{DTIME}(2^{kn})$ has p-measure zero, so $\mathsf{DTIME}(2^{kn})\subsetneq\mathsf{E}$.

## Proof sketch

Diagonalize against $d$: define $A$ bit by bit, always choosing the bit on which $d$ does not increase; computing $d$ to polynomial precision on prefixes of length $2^{O(n)}$ keeps $A$ in $\mathsf{E}$, and $d$ stays bounded along $A$. For $\mathsf{DTIME}(2^{kn})$, a p-martingale betting on the predictions of the first machines succeeds on all their languages.

## Depends on

- [Lutz's resource-bounded measure](resource-bounded-measure.md)
- [Deterministic time classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Jack H. Lutz, "Almost everywhere high nonuniform complexity", Journal of Computer and System Sciences 44(2), 1992, Theorem 3.13 and Corollary 3.14 (stated with density functions, equivalent to martingales).
- Jack H. Lutz, "The Quantitative Structure of Exponential Time", in Complexity Theory Retrospective II, Springer, 1997, Theorem 3.3 and Corollary 5.3 (almost every language in $\mathsf{E}$ has $\{0,1\}^*$ as a $\mathsf{DTIME}(2^{cn})$-complexity core, so $\mathsf{DTIME}(2^{cn})$ has measure zero in $\mathsf{E}$).
