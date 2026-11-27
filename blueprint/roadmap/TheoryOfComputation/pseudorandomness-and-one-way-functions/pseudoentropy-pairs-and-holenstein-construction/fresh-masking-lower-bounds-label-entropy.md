# Fresh masking lower-bounds the conditional entropy of a label

Let $(X, B)$ be a pair of an observation and a bit, and let $\mu(x, b) \in [0,1]$ be a mask probability (possibly depending on the input and the label). Draw a mask coin $c$ with $\Pr[c = 1] = \mu(X, B)$ and set $B' = u$ for a fresh uniform bit $u$ if $c = 1$, and $B' = B$ otherwise. Then

$$H(B' \mid X) \ge \mathbb{E}[\mu(X, B)].$$

Each occurrence draws a fresh mask, even for repeated inputs.

## Proof sketch

Conditioned on $X = x$, the bit $B'$ is uniform with probability at least the conditional mask density, and the binary entropy function is at least the mixing weight of the uniform component by concavity; average over $x$.

## Depends on

- [Samplable pseudoentropy pair with a prediction gap](samplable-pseudoentropy-pair.md)
- [Conditional entropy of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
- T. Holenstein, "Key Agreement from Weak Bit Agreement", Proceedings of the 37th Annual ACM Symposium on Theory of Computing (STOC), 2005.
