# Communication lower bound for lopsided set disjointness

Fix $\delta > 0$. In every bounded-error randomized protocol for $\mathrm{LSD}_{N, B}$, either Alice sends at least $\delta N \log_2 B$ bits or Bob sends at least $N B^{1 - O(\delta)}$ bits. The tradeoff is tight up to constants in the exponent: Alice can send her whole set using $N \log_2 B$ bits, and Bob can send his whole set using $NB$ bits.

## Proof sketch

Pătraşcu proves the randomized bound by a direct-sum style information argument over the $N$ blocks combined with a richness-type rectangle bound per block under a product distribution where Bob's set has density $B^{-\delta}$: a protocol in which Alice reveals $o(\log_2 B)$ bits per block leaves her element in each block nearly uniform among $B^{1-O(\delta)}$ candidates, and Bob must then reveal his membership bits on most of them.

## Depends on

- [Lopsided set disjointness](lopsided-set-disjointness.md)
- [Richness lemma](richness-lemma.md)
- [Distributional communication complexity](../randomized-communication-protocols/dist-complexity.md)

## Proof depends on

- [Lopsided set disjointness](lopsided-set-disjointness.md)
- [Richness lemma](richness-lemma.md)
- [Distributional communication complexity](../randomized-communication-protocols/dist-complexity.md)

## Sources

- Mihai Pătraşcu, "Unifying the Landscape of Cell-Probe Lower Bounds", SIAM Journal on Computing 40(3) (2011); FOCS (2008), arXiv:1010.3783.
