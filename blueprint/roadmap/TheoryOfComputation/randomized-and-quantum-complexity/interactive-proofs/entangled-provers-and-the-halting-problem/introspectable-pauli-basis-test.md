# Pauli basis test with polylogarithmic question length

For every $n$ there is a synchronous game $\mathrm{PB}_n$ with conditionally linear question distribution, questions of length $\mathrm{polylog}(n)$ and answers of length $\mathrm{poly}(n)$, sampled and decided in time $\mathrm{poly}(n)$, such that

- (completeness) the honest strategy that shares $n$ EPR pairs and answers question type $W \in \{X, Z\}$ by measuring all $n$ qubits in the corresponding Pauli basis wins with probability $1$;
- (soundness) every strategy winning with probability $1 - \varepsilon$ is, up to a local isometry on each prover, $\delta$-close in the state-dependent norm to the honest strategy tensored with an auxiliary state, where $\delta \le a\,(\log(n)^{a}\,\varepsilon^{b} + \log(n)^{-b})$ for universal constants $a \ge 1$ and $0 < b \le 1$.

## Proof sketch

Answers are interpreted as evaluations of low individual degree polynomials over a field of characteristic $2$ encoding the $n$-bit Pauli measurement outcomes. The quantum soundness of the low-degree (tensor code) test shows that near-optimal provers measure according to a single global projective measurement with outcomes in the code. Anticommutation between $X$- and $Z$-type answers is certified by Pauli braiding style consistency checks on random lines, and the Gowers-Hatami stability theorem rounds the resulting approximate representation of the Pauli group to an exact one.

## Depends on

- [Conditionally linear question distributions](conditionally-linear-question-distributions.md)
- [Synchronous two-prover games](synchronous-two-prover-games.md)

## Sources

- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "MIP* = RE", Communications of the ACM 64(11) (2021); arXiv:2001.04383.
- Anand Natarajan, Thomas Vidick, "Low-degree testing for quantum states, and a quantum entangled games PCP for QMA", FOCS (2018); arXiv:1801.03821.
- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen, "Quantum soundness of testing tensor codes", Discrete Analysis (2022), FOCS (2021); arXiv:2111.08131.
