# Lifting with low-discrepancy gadgets

For every fixed $\eta > 0$ there is $k = O(1/\eta)$ such that the following holds. Let $g : [m] \times [m] \to \{0,1\}$ be any gadget with uniform discrepancy at most $m^{-\eta}$ and $m \ge n^{2048 k^2}$. If $R \circ g^n$ has a deterministic protocol of cost $c$, then $R$ has a decision tree of depth $d$ with $m^d \le 8^{256 k c}$, so $D^{cc}(R \circ g^n) = \Omega_\eta\big(D^{dt}(R) \log m\big)$. This applies to the inner product gadget on $b$-bit strings, which has discrepancy $2^{-b/2}$.

## Proof sketch

Follow the simulation of the index-gadget proof with density replaced by a discrepancy-based notion: low discrepancy implies that conditioning on rare gadget outputs ("dangerous values") is unlikely, and counting canonical parity tests shows that a dense set has few unsafe values, so each density-restoring step costs few queries per bit of communication. The XOR bound on discrepancy controls the parity tests.

## Depends on

- [Index gadget and lifted search problems](index-gadget-and-lifted-search-problems.md)
- [Discrepancy of a function under a distribution](../discrepancy-corruption-and-sign-rank/discrepancy-under-a-distribution.md)

## Proof depends on

- [XOR products have exponentially small discrepancy](../discrepancy-corruption-and-sign-rank/xor-products-and-discrepancy.md)
- [Low-discrepancy gadgets extract from independent min-entropy sources](../discrepancy-corruption-and-sign-rank/low-discrepancy-gadgets-are-extractors.md)
- [Density-restoring partition](density-restoring-partition.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing 50(1), 2021.
