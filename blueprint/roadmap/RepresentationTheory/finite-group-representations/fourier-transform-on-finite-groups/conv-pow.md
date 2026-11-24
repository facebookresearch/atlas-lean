# Convolution powers on a finite group

Let $G$ be a finite group, $R$ a semiring and $Q : G \to R$. The convolution powers
$Q^{*k} : G \to R$ are defined by $Q^{*0} = \delta_1$, the function equal to $1$ at the identity
and $0$ elsewhere, and $Q^{*(k+1)} = Q * Q^{*k}$, where $*$ is the [convolution](conv.md)
$(P * Q)(s) = \sum_{t \in G} P(s t^{-1})\, Q(t)$.

When $R = \mathbb{R}$ and $Q$ is a probability distribution on $G$, with nonnegative values summing
to $1$, $Q^{*k}$ is the law after $k$ steps of the random walk on $G$ driven by $Q$ (Diaconis,
Saint-Flour notes 1988, Section 2: $Q^{*k} = Q * Q^{*(k-1)}$).
