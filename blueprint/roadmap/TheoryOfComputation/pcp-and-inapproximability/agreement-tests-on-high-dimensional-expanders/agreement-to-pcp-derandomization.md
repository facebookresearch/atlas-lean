# Low-soundness agreement tests yield derandomized parallel repetition for label cover

Bafna–Minzer–Vyas: for every $\delta > 0$ there are $C = C(\delta) > 0$ and a polynomial-time procedure that maps a 3-SAT instance $\varphi$ of size $n$ to a label-cover instance $\Psi$ of size at most $n(\log n)^{C}$ over an alphabet of size $O_\delta(1)$, such that $\operatorname{val}(\Psi) = 1$ if $\varphi$ is satisfiable and $\operatorname{val}(\Psi) \le \delta$ otherwise. Its gap-amplification step is derandomized parallel repetition along the $k$-faces of a high-dimensional expander of polylogarithmic degree whose $k$-faces admit a low-acceptance agreement theorem; this step applies only to a 2-CSP whose constraint graph is the underlying graph of that expander, and a low-acceptance agreement theorem alone does not supply such a 2-CSP.

## Proof sketch

Start from a 2-query PCP with constant soundness $1 - \Omega(1)$, viewed as a 2-CSP. Embed it into a 2-CSP on the underlying graph of the expander, preserving soundness, by simulating each constraint through edge-fault-tolerant routing protocols on that graph. Then repeat along the $k$-faces: a prover strategy for the repeated instance with value above $\delta$ is a local ensemble passing the agreement test, the agreement theorem decodes a global assignment consistent with many local views, and expansion shows that this assignment satisfies most constraints of the embedded 2-CSP, contradicting its soundness. Finally, alphabet reduction brings the alphabet to size $O_\delta(1)$.

## Depends on

- [High-soundness and low-soundness agreement theorems](agreement-soundness-regimes.md)

## Proof depends on

- [Dikstein–Dinur–Lubotzky: linear-size low-acceptance agreement tests](ddl-linear-size-agreement.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Sources

- M. Bafna, D. Minzer, N. Vyas, "Quasi-linear size PCPs with small soundness from HDX", STOC (2025), arXiv:2407.12762.
- Y. Dikstein, I. Dinur, A. Lubotzky, "Low acceptance agreement tests via bounded-degree symplectic HDXs", FOCS (2024), arXiv:2402.01078.
- R. Impagliazzo, V. Kabanets, A. Wigderson, "New direct-product testers and 2-query PCPs", SIAM Journal on Computing 41 (2012) 1722-1768.
- I. Dinur, D. Steurer, "Direct product testing", CCC (2014), ECCC TR13-179.
