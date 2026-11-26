# Natarajan–Vidick Pauli braiding test

The Pauli braiding test combines linearity tests in the $X$ and $Z$ bases with CHSH-style anticommutation tests on random pairs of strings and consistency checks. Honest players holding $n$ EPR pairs and measuring tensor products of Pauli $X$ and $Z$ operators win with probability $1$. Conversely, if a strategy wins with probability at least $1 - \varepsilon$, then there is a local isometry under which Alice's measurements are $O(\mathrm{poly}(\varepsilon))$-close on the state to the Pauli observables $X(a) Z(b)$, $a, b \in \mathbb{F}_2^n$, on a state close to $n$ EPR pairs tensored with an auxiliary state; the error does not depend on $n$.

## Proof sketch

The linearity rounds give exact representations $X(a)$ and $Z(b)$ of $\mathbb{F}_2^n$ close to the strategy; the anticommutation rounds, analysed through CHSH rigidity, force $X(a)Z(b) = (-1)^{\langle a,b\rangle} Z(b)X(a)$ approximately; a stability theorem for approximate representations of the Pauli group then gives the isometry extracting EPR pairs.

## Depends on

- [Quantum soundness of the two-player linearity test](quantum-soundness-of-the-linearity-test.md)
- [Rigidity of near-optimal CHSH strategies](rigidity-of-near-optimal-chsh-strategies.md)

## Proof depends on

- [Quantum soundness of the two-player linearity test](quantum-soundness-of-the-linearity-test.md)
- [Rigidity of near-optimal CHSH strategies](rigidity-of-near-optimal-chsh-strategies.md)
- [Projective strategies suffice (Naimark dilation)](projective-strategies-suffice.md)

## Sources

- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017.
