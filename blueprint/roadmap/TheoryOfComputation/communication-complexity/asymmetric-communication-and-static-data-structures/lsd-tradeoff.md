# Communication lower bound for lopsided set disjointness

Fix $\delta > 0$. In every bounded-error randomized protocol for $\mathrm{LSD}_{N, B}$, either Alice sends at least $\delta N \log_2 B$ bits or Bob sends at least $N B^{1 - O(\delta)}$ bits. The tradeoff is tight up to constants in the exponent: Alice can send her whole set using $N \log_2 B$ bits, and Bob can send his whole set using $NB$ bits.

## Proof sketch

The deterministic version follows from the richness lemma (Miltersen et al.). For bounded-error protocols, Pătraşcu uses a hard distribution on blocked instances: Alice's set has one element per block and Bob's set contains exactly one element of each pair $\{(i, 2j), (i, 2j+1)\}$ of every block $i$, so Bob holds half of each block. Conditioned on auxiliary variables recording, block by block, which side was sampled first, the two inputs are independent, so the transcript reveals at most $a$ bits about Alice's set and $b$ bits about Bob's; a direct-sum argument then yields a protocol for a single block in which Alice reveals $O(a/N)$ and Bob $O(b/N)$ bits of information. A rectangle-style lemma for one block shows that if Alice reveals at most $\delta\log_2 B$ bits, Bob must reveal $B^{1 - O(\delta)}$ bits for the error to stay small, which gives the tradeoff.

## Depends on

- [Lopsided set disjointness](lopsided-set-disjointness.md)
- [Asymmetric $[a, b]$-protocols](asymmetric-protocol.md)
- [Randomized protocol](../randomized-communication-protocols/randomized-protocol.md)

## Proof depends on

- [Richness lemma](richness-lemma.md)
- [Distributional communication complexity](../randomized-communication-protocols/dist-complexity.md)

## Sources

- Mihai Pătraşcu, "Unifying the Landscape of Cell-Probe Lower Bounds", SIAM Journal on Computing 40(3) (2011); FOCS (2008), arXiv:1010.3783.
