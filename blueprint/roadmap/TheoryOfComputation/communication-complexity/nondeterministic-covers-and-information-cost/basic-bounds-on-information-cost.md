# Basic bounds on information cost

For every protocol $\pi$ with transcript $\Pi = (R, M)$ (public randomness $R$, messages $M$) and input distribution $\mu$:

1. $I(\Pi; XY) = I(M; XY \mid R) \le H(M \mid R) \le \mathbb{E}|M| \le \mathrm{cost}(\pi)$, and for each fixed value $r$ of $R$, $I(M; XY \mid R = r) \le \log_2 (\#\text{message transcripts at } r) \le \mathrm{cost}(\pi)$;
2. $I(\Pi; XY) - \big(I(\Pi; X\mid Y) + I(\Pi; Y \mid X)\big) = I(X; Y) - I(X; Y \mid \Pi) \ge 0$;
3. if $X$ and $Y$ are independent under $\mu$, then $I(X; Y \mid \Pi) = 0$ and the internal and external costs are equal;
4. information costs depend only on the joint law of inputs and transcript, so they are invariant under injective relabelling of transcripts.

## Proof sketch

(1) $R$ is independent of $(X, Y)$, so $I(\Pi; XY) = I(M; XY \mid R)$; mutual information is at most conditional entropy, and at fixed $R = r$ the message transcripts form a prefix-free set, so their entropy is at most their expected length and at most the logarithm of their number. (2) The identity is the chain rule. For the inequality, condition on $R$ (which leaves $I(X;Y)$ unchanged) and reveal the messages bit by bit. At an Alice node with prefix $P$ and next bit $B$, the bit is a function of $X$, $P$ and Alice's private coins, which are conditionally independent of $Y$ given $(X, P)$ because the event of reaching $P$ is a product of an Alice part and a Bob part; so $I(B; Y \mid X, P) = 0$ and $I(X; Y \mid P, B) = I(X; Y \mid P) - I(B; Y \mid P) \le I(X; Y \mid P)$. Bob nodes are symmetric. Conditioning on a transcript need not make correlated inputs independent: for $X = Y$ a fair bit and no messages, $I(X; Y \mid \Pi) = 1$. (3) With $I(X;Y) = 0$, (2) forces $I(X; Y \mid \Pi) = 0$ and the difference is zero.

## Depends on

- [Internal and external information cost](internal-and-external-information-cost.md)

## Sources

- M. Braverman and A. Rao, "Information Equals Amortized Communication", FOCS 2011; ECCC report TR10-083.
- A. Rao and A. Yehudayoff, "Communication Complexity and Applications", Cambridge University Press, 2020.
