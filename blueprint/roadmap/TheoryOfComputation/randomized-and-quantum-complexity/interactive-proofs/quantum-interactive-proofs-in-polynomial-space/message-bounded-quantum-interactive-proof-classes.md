# Message-bounded quantum interactive proof classes QIP(m)

For a polynomially bounded $m(n)$ and $0 \le s < c \le 1$, a promise problem $(L_{yes}, L_{no})$ is in $\mathrm{QIP}_{c,s}(m)$ if there is a polynomial-time uniformly generated quantum verifier exchanging at most $m(|x|)$ quantum messages (of polynomially many qubits) with an unbounded quantum prover, such that some prover makes the verifier accept every $x \in L_{yes}$ with probability at least $c$, and every prover makes it accept every $x \in L_{no}$ with probability at most $s$. Write $\mathrm{QIP}(m) = \mathrm{QIP}_{2/3,1/3}(m)$ and $\mathrm{QIP} = \bigcup_{p} \mathrm{QIP}(p)$ over polynomials $p$.

## Depends on

- [Quantum interactive proofs (QIP) and IP subset QIP](../../quantum-interactive-proofs-and-ip-subset-qip.md)
- [Quantum interaction semantics](../../quantum-interaction-semantics.md)

## Sources

- Alexei Kitaev, John Watrous, "Parallelization, amplification, and exponential time simulation of quantum interactive proof systems", STOC (2000).
- Rahul Jain, Zhengfeng Ji, Sarvagya Upadhyay, John Watrous, "QIP = PSPACE", Journal of the ACM 58(6) (2011), STOC (2010); arXiv:0907.4737.
