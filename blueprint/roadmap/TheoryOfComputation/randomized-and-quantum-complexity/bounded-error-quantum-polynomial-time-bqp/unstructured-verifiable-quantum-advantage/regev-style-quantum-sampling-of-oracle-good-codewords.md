# Quantum algorithm for codeword search via dual decoding

Let $C \subseteq \Sigma^n$, $\Sigma=\mathbb{F}_q^m$ with $|\Sigma|=\omega(\log n)$, be an $\mathbb{F}_q$-linear (folded) code with dual $C^\perp$, and suppose there is a classical polynomial-time algorithm $\mathrm{Dec}$ such that, for $e\in\Sigma^n$ whose coordinates are independent, each equal to $0$ with probability $1/2$ and otherwise uniform on $\Sigma\setminus\{0\}$, $\Pr_e[\forall x\in C^\perp:\ \mathrm{Dec}(x+e)=x]=1-\mathrm{negl}(n)$ (this error law approximates the one induced by the Fourier transform of the indicator of $\{\sigma : H_i(\sigma) = 1\}$). Then a quantum polynomial-time algorithm with superposition access to $H$ solves $\mathrm{YZ}^H_C$ with probability $1 - \mathrm{negl}(n)$ over $H$.

## Proof sketch

Prepare $\bigotimes_i \big(\sum_{\sigma : H_i(\sigma) = 1} |\sigma\rangle\big)$ by computing $H$ in superposition and postselecting coordinatewise (each coordinate succeeds with probability about $1/2$, done by amplitude amplification per coordinate). Applying the quantum Fourier transform over $\Sigma^n$, the goal state $\sum_{x \in C,\, H_i(x_i) = 1}|x\rangle$ corresponds to a superposition over $C^\perp$ plus Fourier-domain errors; as in Regev's reduction, decoding $C^\perp$ in superposition uncomputes the error register, and an inverse Fourier transform followed by measurement yields a uniformly random valid codeword.

## Depends on

- [The Yamakawa-Zhandry codeword search problem](yamakawa-zhandry-codeword-search-problem.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
- Oded Regev, "On lattices, learning with errors, random linear codes, and cryptography", Journal of the ACM 56(6) (2009).
