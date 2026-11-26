# Computational knowledge complexity k(n) of an interactive proof

An interactive proof system $(P,V)$ for a promise problem $\Pi=(\Pi_{\mathrm{yes}},\Pi_{\mathrm{no}})$ has **computational knowledge complexity $k(n)$** if there are a probabilistic polynomial-time algorithm $S$ and a family of functions $\kappa_n:\{0,1\}^n\times\{0,1\}^{\mathrm{poly}(n)}\to\{0,1\}^{k(n)}$ such that for every $x\in\Pi_{\mathrm{yes}}$ the distribution of $S(x,\kappa_{|x|}(x,r);r)$ for $r\sim\{0,1\}^{\mathrm{poly}(|x|)}$ is computationally indistinguishable from the verifier's view of the interaction of $P$ and $V$ on common input $x$. Knowledge complexity $0$ is computational zero knowledge; the definition is equivalent to the oracle formulation of Goldreich and Petrank, in which the simulator may query $k(n)$ advice bits. $\mathsf{CZK}$ denotes the promise problems with computational zero-knowledge proofs, $\mathsf{SZKA}$ and $\mathsf{CZKA}$ the analogues for argument systems (soundness only against efficient provers).

## Depends on

- [Zero-knowledge interactive proofs](../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Statistical honest-verifier zero knowledge](../../../ComputerScience/cryptography/signatures-and-protocols/zero-knowledge-proofs/stat-hvzk.md)

## Sources

- Shuichi Hirahara and Mikito Nanashima, "One-Way Functions and Zero Knowledge", STOC (2024), ECCC TR24-063.
