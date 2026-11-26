# Cross-examination debate with a stochastic oracle

Consider a randomized computation given by a step law: from the bits written so far, a distribution of the next bit, with output the final bit. In the cross-examination debate, a proposer and a challenger argue about the output in front of a verifier who samples the law at only one step selected through the provers' claims. If the output is $1$ with probability at least $2/3$, the honest proposer wins with probability at least $3/5$ against every challenger; if the output is $1$ with probability at most $1/3$ and the step law is Lipschitz at the relevant points, every proposer loses to the honest challenger except with probability at most $2/5$. Both honest strategies need only polynomially many oracle samples ('doubly efficient' debate).

## Proof sketch

The proposer commits to conditional acceptance probabilities along the run; the challenger points to a step where the claimed probabilities are inconsistent with the step law by more than a threshold; the verifier samples that step to estimate the discrepancy. A Lipschitz condition bounds how errors propagate, so a false global claim forces a large local discrepancy at some step.

## Depends on

- [The class IP](../../complexity-classes/time-and-space-complexity-classes/ip.md)

## Sources

- Jonah Brown-Cohen, Geoffrey Irving and Georgios Piliouras, "Scalable AI Safety via Doubly-Efficient Debate", Proceedings of the 41st International Conference on Machine Learning, arXiv:2311.14125, 2024, Section 6 and Appendix D.
