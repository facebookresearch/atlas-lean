# Chia–Chou–Zhang–Zhang: SZK is in BPP with an MQCSP oracle

Statistical zero knowledge reduces to the quantum circuit minimization problem: $\mathsf{SZK}\subseteq\mathsf{BPP}^{\mathrm{MQCSP}}$, extending the Allender–Das theorem for classical MCSP even though the two problems are incomparable.

**Theorem.** $\mathsf{SZK}\subseteq\mathsf{BPP}^{\mathrm{MQCSP}}$.

Here an SZK promise problem has a probabilistic polynomial-time verifier with completeness $2/3$, soundness $1/3$ and a simulator whose output is negligibly close in statistical distance to every verifier's view on yes instances. The proof uses the SZK-complete problem Polarized Image Intersection Density (PIID) of Ben-Or and Gutfreund: given circuits $C_0,C_1:\{0,1\}^{m}\to\{0,1\}^{m'}$ of size $n^{k}$, decide whether $\max_{S}|\Pr_x[C_0(x)\in S]-\Pr_x[C_1(x)\in S]|\le 1/2^{n}$ or $\Pr_x[\exists y\in\mathrm{Im}(C_0),\ C_1(x)=y]\le 1/2^{n}$, where $n=\mathrm{poly}(m)$.

## Expansion

Two facts replace their classical counterparts: small classical circuits give small quantum circuits, so truth tables of pseudorandom function families have low quantum circuit complexity; and an MQCSP oracle inverts one-way functions on average, because a quantum algorithm for MQCSP breaks quantum-secure pseudorandom generators built from them, in the style of Kabanets–Cai and Razborov–Rudich. With this inverter one solves PIID by following the Allender–Das framework: pick a uniform $x$, use the MQCSP-based inverter for $f_1=C_1$ on $C_0(x)$ to get $x'$, and accept iff $C_1(x')=C_0(x)$. On no instances $C_0(x)$ has a $C_1$-preimage with probability at most $1/2^{n}$; on yes instances $C_0(x)$ is distributed close to $C_1$ of a uniform input, which is exactly where the inverter succeeds.

## Depends on

- [The Minimum Quantum Circuit Size Problem MQCSP](minimum-quantum-circuit-size-problem.md)

## Proof depends on

- [Chia–Chou–Zhang–Zhang: MQCSP in BQP rules out quantum-secure one-way functions](mqcsp-in-bqp-rules-out-quantum-secure-one-way-functions.md)
- [Kabanets–Cai: if MCSP is in BPP, there are no one-way functions](../../meta-complexity-and-one-way-functions/kabanets-cai-mcsp-in-bpp-rules-out-owfs.md)

## Sources

- Nai-Hui Chia, Chi-Ning Chou, Jiayu Zhang and Ruizhe Zhang, "Quantum Meets the Minimum Circuit Size Problem", *13th Innovations in Theoretical Computer Science Conference (ITCS 2022)*, LIPIcs, 2022, https://doi.org/10.4230/LIPIcs.ITCS.2022.47; numbering from arXiv:2108.03171v3 (Definitions 3.10, 3.11 and 3.12, Theorem 3.13, Appendix A).
