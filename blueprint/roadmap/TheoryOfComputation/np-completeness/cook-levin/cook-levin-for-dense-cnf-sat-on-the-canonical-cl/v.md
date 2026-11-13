# Input-bit symbol of the verifier

Let $V$ be a polynomial-time machine computing a
function of pairs of bit lists from their pair encoding, whose input alphabet is identified with
the pair alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$, and let $\beta$ be the
fixed bijection from $\{0, 1\}$ onto the Booleans. For an index $i \in \{0, 1\}$, this is the
symbol of $V$'s input alphabet that corresponds to the left-tagged bit $\mathrm{inl}(\beta(i))$.
