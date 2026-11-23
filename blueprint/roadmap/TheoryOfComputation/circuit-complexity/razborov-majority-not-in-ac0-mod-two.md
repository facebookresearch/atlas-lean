# Razborov: majority is not in AC0[mod 2]

The majority language, which accepts a bitstring exactly when more of its entries are true than false, is not in $\mathsf{AC}^0[2]$: no family of polynomial-size, bounded-depth, well-formed flat Boolean circuits with and, or, not gates and mod gates of modulus $2$ decides it.

Razborov approximates every gate of such a circuit by a polynomial of low degree over $\mathbb{F}_2$, so that the whole circuit agrees with a low-degree polynomial on most inputs, and shows that majority is far from every such polynomial. Smolensky extended the method to mod gates of any prime modulus $p$, which cannot compute $\mathrm{MOD}_q$ when $q$ is not a power of $p$; [parity is not in $\mathsf{AC}^0[3]$](smolensky.md) is the case $p = 3$, $q = 2$.

## Sources

- A. A. Razborov, "Lower bounds on the size of bounded depth networks over a complete basis with logical addition", Mat. Zametki 41 (1987), 598-607; English translation Math. Notes 41 (1987), 333-338.
