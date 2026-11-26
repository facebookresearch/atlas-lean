# Low-soundness agreement tests yield derandomized parallel repetition for label cover

Let $\mathcal{F}$ be a $k$-uniform set family over the variables of a projection label-cover instance $\mathcal{L}$ admitting a low-acceptance agreement theorem with soundness $\delta$ and size $|\mathcal{F}| = O(|\mathcal{L}|)$. Then the derandomized direct product of $\mathcal{L}$ along $\mathcal{F}$ is a label-cover instance $\mathcal{L}^{\mathcal{F}}$ of size $O_k(|\mathcal{L}|)$ such that if $\mathcal{L}$ is satisfiable so is $\mathcal{L}^{\mathcal{F}}$, and if $\operatorname{val}(\mathcal{L}) \le 1 - \gamma$ then $\operatorname{val}(\mathcal{L}^{\mathcal{F}}) \le \max\bigl(\delta,\ \exp(-\Omega(\gamma k))\bigr)$. Combined with the linear-size agreement tests, this gives gap amplification with only linear blow-up, a step towards linear-size PCPs with small soundness.

## Proof sketch

A prover strategy for $\mathcal{L}^{\mathcal{F}}$ with value above $\delta$ is a local ensemble passing an agreement test embedded in the verifier; the agreement theorem decodes a global labeling $G$ consistent with many local views, and a sampling argument over the constraints inside sets of $\mathcal{F}$ shows that $G$ satisfies a $1 - O(\gamma)$ fraction of constraints of $\mathcal{L}$ unless the soundness bound holds.

## Depends on

- [Dikstein–Dinur–Lubotzky: linear-size low-acceptance agreement tests](ddl-linear-size-agreement.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Proof depends on

- [Dikstein–Dinur–Lubotzky: linear-size low-acceptance agreement tests](ddl-linear-size-agreement.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../pcp-theorem.md)

## Sources

- Y. Dikstein, I. Dinur, A. Lubotzky, "Low acceptance agreement tests via bounded-degree symplectic HDXs", FOCS (2024), arXiv:2402.01078.
- R. Impagliazzo, V. Kabanets, A. Wigderson, "New direct-product testers and 2-query PCPs", SIAM Journal on Computing 41 (2012) 1722-1768.
- I. Dinur, D. Steurer, "Direct product testing", CCC (2014), ECCC TR13-179.
