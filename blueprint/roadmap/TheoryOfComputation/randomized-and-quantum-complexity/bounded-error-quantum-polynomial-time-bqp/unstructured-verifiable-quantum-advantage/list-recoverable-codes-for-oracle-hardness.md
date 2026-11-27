# List-recoverable codes

A code $C \subseteq \Sigma^n$ is *$(\zeta, \ell, L)$-list recoverable* if for all sets $S_1, \dots, S_n \subseteq \Sigma$ with $|S_i| \le \ell$, at most $L$ codewords $c \in C$ satisfy $c_i \in S_i$ for at least $(1 - \zeta)n$ indices $i$. For $\zeta = 0$ this is *zero-error list recovery*: $|\{c \in C : c_i \in S_i \ \forall i\}| \le L$.

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
- Venkatesan Guruswami, Atri Rudra, "Explicit codes achieving list decoding capacity: error-correction with optimal redundancy", IEEE Transactions on Information Theory 54(1) (2008).
