# From pseudorandom states with logarithmic output length to classical pseudorandom strings

A pseudodeterministic quantum pseudorandom generator (QPRG) is a quantum polynomial-time algorithm $G$ mapping a seed to a classical string of greater length such that, for all but a $\mu(\lambda)=O(\lambda^{-c'})$ fraction of seeds, one fixed string is output with probability at least $1-\mu(\lambda)$ (pseudodeterminism). It is *weak* if every quantum polynomial-time distinguisher has advantage at most $1-1/\mathrm{poly}(\lambda)$ between $G$ on a uniform seed and a uniform string, and *strong* if that advantage is negligible.

**Theorem (Ananth–Lin–Yuen, Corollary 4.6).** If $(c\log\lambda)$-qubit pseudorandom states exist for some constant $c>12$, then there is a strong QPRG $G:\{0,1\}^{\lambda^2}\to\{0,1\}^{\lambda^{c/6}}$, with output length $\lambda^{c/6}>\lambda^2$ exceeding the seed length, and pseudodeterminism $1-O(\lambda^{-(c/12-1)})$. Under $(c\log\lambda)$-qubit PRS for a constant $c>6$ alone, Theorem 4.2 gives only a *weak* QPRG with seed length $\lambda$, output length $\lambda^{c/6}$, pseudodeterminism $1-O(\lambda^{-c/12})$ and distinguishing advantage $O(\lambda^{-c/6})$, inverse-polynomial rather than negligible. An arbitrary $O(\log\lambda)$ bound does not suffice as a hypothesis: it includes the small-coefficient regime where short PRS exist unconditionally. QPRGs give statistically binding, computationally hiding quantum commitments and pseudo one-time pads.

## Proof sketch

With logarithmically many qubits, polynomially many copies of $|\phi_k\rangle$ determine its measurement statistics to inverse-polynomial accuracy, and the key step is a procedure that, from such copies, pseudodeterministically extracts a string that is close to uniform when the state is Haar random; pseudorandomness of the PRS then transfers to the extracted strings, giving the weak QPRG. XORing the outputs of $\lambda$ independent copies on a $\lambda^2$-bit seed amplifies weak to strong security at the cost of the stated loss in pseudodeterminism.

## Depends on

- [Pseudorandom quantum state generators](pseudorandom-quantum-states.md)

## Sources

- Prabhanjan Ananth, Yao-Ting Lin, Henry Yuen, "Pseudorandom Strings from Pseudorandom Quantum States", ITCS (2024), IACR ePrint 2023/904; arXiv:2306.05613 (Definition 4.1, Theorem 4.2, Corollary 4.6).
