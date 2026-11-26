# Constant-frame catalytic equality of n-bit identifiers

Let $B\ge 2$ and $n\le C\cdot B$ for a constant $C$. Two $n$-bit identifiers $x,y$, each available only during separate 'excursions', can be compared for equality by an exact deterministic procedure making $64$ excursions, using shared catalytic memory consisting of two register banks and a table $W:\mathbb{Z}/2^{k_2}\to\mathbb{Z}/2$ with $2^{k_2}=O(B)$, all restored exactly, while the caller keeps only $7$ local bits (a phase in $\{0,\dots,63\}$ and one result bit). It chunks the identifiers into $\lfloor\log_2 B\rfloor$-bit digits, applies the sum-of-squares test twice in nested stages to shrink the difference indicator to an $O(\log B)$-bit accumulator alternating between two values, and finally toggles the table $W$ at those values, which changes the result bit iff $x=y$.

## Proof sketch

Each stage alternates the signed call of the previous stage four times so that its accumulator takes the values $z,z',z,z'$ without being stored, and feeds those values to the next sum-of-squares test; the final key test toggles $W$ at $z$ and at $z'$ around reading it, which leaves $W$ unchanged and isolates $[z=z']$.

## Depends on

- [Catalytic space computation](catalytic-space.md)

## Proof depends on

- [Catalytic equality test by four alternating visits](catalytic-sum-of-squares-equality-test.md)

## Sources

- OpenAI, "Exact Derandomization of Logarithmic Space: L = RL = BPL", Preprint, 2026.
