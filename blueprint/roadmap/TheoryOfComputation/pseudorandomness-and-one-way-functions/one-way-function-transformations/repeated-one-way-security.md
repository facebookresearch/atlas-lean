# One-wayness survives polynomially many published instances with adaptive reveals

If $f$ is one-way on $n$-bit inputs, then for every polynomial $t(n)$ every probabilistic polynomial-time adversary wins the repeated inversion game with negligible probability. Quantitatively, an adversary with success $\varepsilon$ yields an inverter for $f$ with success at least $\varepsilon / t(n)$.

## Proof sketch

The inverter plants its challenge at a uniformly random slot $j^*$ and samples the other instances itself, so it can answer every reveal request except at $j^*$. If the adversary never requests slot $j^*$ and outputs $j = j^*$, the inverter wins; the slot is guessed correctly with probability $1/t(n)$, independently of the adversary's view.

## Depends on

- [Repeated inversion game for a one-way function](repeated-inversion-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
