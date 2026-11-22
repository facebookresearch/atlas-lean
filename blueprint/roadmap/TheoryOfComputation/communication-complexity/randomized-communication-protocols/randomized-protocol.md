# Randomized protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. A randomized protocol is a finitely supported probability distribution on protocols, that is, weights
$\pi(p) \ge 0$, nonzero for only finitely many protocols $p$, with $\sum_p \pi(p) = 1$. The protocol run is
drawn from $\pi$ independently of the inputs, and both parties see the draw.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 3: "a randomized protocol can be thought of as a distribution on deterministic protocols".
