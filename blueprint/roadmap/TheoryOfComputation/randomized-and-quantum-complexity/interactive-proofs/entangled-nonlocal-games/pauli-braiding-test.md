# Natarajan–Vidick Pauli braiding test

The Pauli braiding test combines linearity tests in the $X$ and $Z$ bases with CHSH-style anticommutation tests on random pairs of strings and consistency checks. Honest players holding $n$ EPR pairs and measuring tensor products of Pauli $X$ and $Z$ operators win with probability $1$. Conversely, if a strategy wins with probability at least $1 - \varepsilon$, then there are absolute constants $C, c > 0$, independent of $n$, and a local isometry under which, on average over uniform $a, b \in \mathbb{F}_2^n$, Alice's observables are within $C\varepsilon^{c}$ in the state-dependent norm of the Pauli observables $X(a) Z(b)$, and the state is within $C\varepsilon^{c}$ of $n$ EPR pairs tensored with an auxiliary state.

## Proof sketch

The linearity rounds give, in each basis, one measurement whose outcome $s$ reproduces the answer $\langle s, a \rangle$ to every string $a$, hence representations $X(a)$ and $Z(b)$ of $\mathbb{F}_2^n$ close to the strategy; the anticommutation rounds, analysed through CHSH rigidity, force $X(a)Z(b) = (-1)^{\langle a,b\rangle} Z(b)X(a)$ approximately; a stability theorem for approximate representations of the Pauli group then gives the isometry extracting EPR pairs.

## Depends on

- [Quantum soundness of the two-player linearity test](quantum-soundness-of-the-linearity-test.md)
- [Rigidity of near-optimal CHSH strategies](rigidity-of-near-optimal-chsh-strategies.md)

## Proof depends on

- [Projective strategies suffice (Naimark dilation)](projective-strategies-suffice.md)

## Sources

- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017.
