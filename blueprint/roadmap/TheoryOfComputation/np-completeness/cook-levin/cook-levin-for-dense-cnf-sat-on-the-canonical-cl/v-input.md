# Input of the verifier on a pair

Let $V$ be a polynomial-time machine computing a function
of pairs of bit lists from their pair encoding, whose input alphabet is identified with the pair
alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$, and let $\beta$ be the fixed
bijection from $\{0, 1\}$ onto the Booleans. For bit lists $a$ and $y$, translating the pair
encoding $a \# y$ symbol by symbol into $V$'s input alphabet gives the input-bit symbols of the
indices $\beta^{-1}(b)$ for the bits $b$ of $a$ in order, then the separator symbol, then the
certificate symbols of the bits of $y$ in order.
