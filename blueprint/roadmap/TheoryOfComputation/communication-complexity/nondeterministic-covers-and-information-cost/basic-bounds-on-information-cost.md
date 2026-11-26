# Basic bounds on information cost

For every protocol $\pi$ and input distribution $\mu$: (1) $I(\Pi; XY) \le \log_2(\#\text{transcripts}) \le \mathrm{cost}(\pi)$; (2) $I(\Pi; XY) - \big(I(\Pi; X\mid Y) + I(\Pi; Y \mid X)\big) = I(X; Y) - I(X; Y \mid \Pi) \ge 0$ for private-coin protocols (rectangle property of transcripts); (3) if $X$ and $Y$ are independent under $\mu$, the internal and external costs are equal; (4) information costs depend only on the joint law of inputs and transcript, so they are invariant under relabelling transcripts.

## Proof sketch

(1) Mutual information is at most the entropy of $\Pi$. (2) Expand both sides by the chain rule; conditioned on a transcript of a private-coin protocol the inputs remain independent given the rectangle structure, giving $I(X;Y \mid \Pi) \le I(X;Y)$. (3) is (2) with $I(X;Y) = 0$.

## Depends on

- [Internal and external information cost](internal-and-external-information-cost.md)

## Sources

- M. Braverman and A. Rao, "Information Equals Amortized Communication", FOCS 2011.
- A. Rao and A. Yehudayoff, "Communication Complexity and Applications", Cambridge University Press, 2020.
