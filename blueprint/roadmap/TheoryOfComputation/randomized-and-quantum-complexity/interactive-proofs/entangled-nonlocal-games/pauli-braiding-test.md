# Natarajan–Vidick Pauli braiding test

Let $G_{ac}$ be an $(\omega^*_{ac}, \delta)$ anticommutation game in the sense of Natarajan and Vidick (Definition 8): its value is at least $\omega^*_{ac}$, an honest strategy on $m$ EPR pairs attains $\omega^*_{ac}$, and every strategy within $\varepsilon$ of $\omega^*_{ac}$ is, up to local isometries, within $\delta(\varepsilon)$ of one using Pauli $X$ and $Z$ on one EPR pair for two special questions. The CHSH game is a $(\cos^2(\pi/8), O(\sqrt\varepsilon))$ anticommutation game with $m = 1$, and the magic square game a $(1, O(\sqrt\varepsilon))$ anticommutation game with $m = 2$ (Lemma 9). The Pauli braiding test with $G_{ac}$ (Figure 2) labels a random player Alice and runs one of three subtests: the two-player linearity test in a basis $W \in \{X, Z\}$; the game $G_{ac}$ on a uniformly random pair $a, b \in \mathbb{F}_2^n$ with $a \cdot b = 1$ sent to both players; and consistency checks between the two kinds of questions. Let $\omega^*_{\mathrm{pauli}} = \frac23 + \frac13\omega^*_{ac}$. The honest players share $|\mathrm{EPR}\rangle^{\otimes n} \otimes |\mathrm{EPR}\rangle^{\otimes (m-1)}$, answer basis questions by measuring tensor products of Pauli $X$ or of Pauli $Z$ on the $n$ EPR pairs, and win with probability $\omega^*_{\mathrm{pauli}}$; this is $1$ exactly when $\omega^*_{ac} = 1$ (the magic square game, $n + 1$ EPR pairs), while with CHSH it is $\frac23 + \frac13\cos^2(\pi/8) < 1$. Conversely, if a strategy wins with probability at least $\omega^*_{\mathrm{pauli}} - \varepsilon$ and $\delta(\varepsilon) = O(\sqrt\varepsilon)$ (as for both games above), then: there is a local isometry after which the state on $n$ extracted qubit pairs has fidelity $1 - O(\varepsilon^{1/8})$ with $n$ EPR pairs (Corollary 16); and on Alice's space extended by ancilla EPR pairs there are observables $P(a, b)$ obeying the Pauli braiding relations $P(a, b)P(a', b') = (-1)^{a' \cdot b} P(a + a', b + b')$ exactly, with Alice's marginal observables $X(a)$ and $Z(b)$ within $O(\varepsilon^{1/8})$ of $P(a, 0)$ and $P(0, b)$ in squared state-dependent distance, on average over uniform $a$ and $b$ (Theorems 13 and 14).

## Proof sketch

The linearity rounds give, in each basis, approximately linear observables $X(a)$ and $Z(b)$ consistent between the players (Theorem 11); the anticommutation rounds, analysed through the soundness of $G_{ac}$ (CHSH rigidity in the CHSH case), force $X(a)Z(b) \approx -Z(b)X(a)$ when $a \cdot b = 1$, and the consistency rounds tie these to the linearity answers (Theorem 13); a stability theorem for approximate representations of the Pauli group then gives exact braiding observables on an extended space, and the EPR overlap follows (Theorem 14, Corollary 16).

## Depends on

- [Quantum soundness of the two-player linearity test](quantum-soundness-of-the-linearity-test.md)
- [Rigidity of near-optimal CHSH strategies](rigidity-of-near-optimal-chsh-strategies.md)
- [The Mermin–Peres magic square game](mermin-peres-magic-square-game.md)

## Proof depends on

- [Projective strategies suffice (Naimark dilation)](projective-strategies-suffice.md)

## Sources

- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017 (arXiv:1610.03574), Definition 8, Lemma 9, Figure 2, Definition 12, Theorems 13 and 14 and Corollary 16.
