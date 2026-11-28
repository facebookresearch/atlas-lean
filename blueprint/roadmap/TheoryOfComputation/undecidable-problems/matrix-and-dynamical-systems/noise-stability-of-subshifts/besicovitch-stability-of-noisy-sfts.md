# Besicovitch stability of noisy subshifts of finite type is Π₂-hard

Whether a subshift of finite type is stable under Bernoulli noise in the Besicovitch distance is undecidable: the problem is $\Pi_2$-hard in the arithmetical hierarchy, and it lies in $\Pi_4$.

**Subshifts of finite type.** Let $\mathcal A$ be a finite alphabet and $d\ge1$. For a finite set $\mathcal F$ of forbidden patterns, each defined on a finite window of $\mathbb Z^d$, the *subshift of finite type* (SFT) $\Omega_{\mathcal F}\subseteq\mathcal A^{\mathbb Z^d}$ is the set of configurations in which no translate of a pattern of $\mathcal F$ occurs. Let $\mathcal M_{\mathcal F}$ be the set of shift-invariant probability measures supported on $\Omega_{\mathcal F}$.

**Noise.** On the alphabet $\mathcal A\times\{0,1\}$, where a cell marked $1$ is *obscured*, forbid only the patterns of $\mathcal F$ whose cells are all unobscured. Let $\mathcal M^{\mathcal B}_{\mathcal F}(\epsilon)$ be the set of projections to $\mathcal A^{\mathbb Z^d}$ of the shift-invariant measures supported on this noisy SFT whose marginal on $\{0,1\}^{\mathbb Z^d}$ is a Bernoulli product measure with probability of $1$ at most $\epsilon$.

**Besicovitch distance.** For configurations $x,y$ let $d_H(x,y)=\limsup_n(2n+1)^{-d}\,\#\{k\in[-n,n]^d : x_k\ne y_k\}$, and for shift-invariant measures $\mu,\nu$ let $d_B(\mu,\nu)=\inf_\lambda\int d_H\,d\lambda$ over all couplings $\lambda$ of $\mu$ and $\nu$. The SFT $\Omega_{\mathcal F}$ is *stable* if there is a nondecreasing $f:[0,1]\to\mathbb R_{\ge0}$, continuous at $0$ with $f(0)=0$, such that

$$
\sup_{\mu\in\mathcal M^{\mathcal B}_{\mathcal F}(\epsilon)}d_B(\mu,\mathcal M_{\mathcal F})\le f(\epsilon)\quad\text{for every }\epsilon\in[0,1].
$$

**Theorem.** Let $P_{\mathrm{stab}}$ be the set of finite families $\mathcal F$ of forbidden patterns whose SFT is stable, each family given with its finite alphabet and dimension $d$ and its patterns as finite tables. There is a computable map $M\mapsto P_2(M)$ from Turing machines to SFTs with $P_2(M)\in P_{\mathrm{stab}}$ iff $M$ halts on every input; hence $P_{\mathrm{stab}}$ is $\Pi_2$-hard (Theorem 5.11 of the source).

The source proves this after a simpler reduction $M\mapsto P_1(M)$ with $P_1(M)\in P_{\mathrm{stab}}$ iff $M$ does not halt on the empty input, so that $P_{\mathrm{stab}}$ is $\Pi_1$-hard and undecidable (Theorem 5.1), and it shows that $P_{\mathrm{stab}}$ is in $\Pi_4$ (Theorem 6.8).

The SFTs produced by the reductions are two-dimensional. A further reduction gives $S_1(M)\in P_{\mathrm{stab}}$ iff $M$ halts on the empty input, so $P_{\mathrm{stab}}$ is also $\Sigma_1$-hard (Proposition 5.7 of the source).

## Depends on

- [Subshifts and the aperiodic domino problem](../../wang-tiles/aperiodic-domino-problem/subshifts-and-the-aperiodic-domino-problem.md)
- [The arithmetical class $\Pi_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [TOT is Π⁰₂-complete and FIN is Σ⁰₂-complete](../../../degrees-and-hierarchies/arithmetical-hierarchy/totality-and-finiteness-index-sets-are-complete.md)

## Expansion

The building block is a red-black variant of the Robinson aperiodic tiling, which the source shows to be unstable: under arbitrarily small noise some invariant measure stays far from every measure of the SFT. Aperiodic SFTs whose almost periodic structure can be reconstructed locally are, in contrast, stable. Embedding Turing machine computations in the Robinson hierarchy, the SFT $P_1(M)$ is made unstable exactly when $M$ halts, and $P_2(M)$ exactly when $M$ fails to halt on some input; since halting is $\Sigma_1$-complete and totality is $\Pi_2$-complete, stability is $\Pi_1$-hard and then $\Pi_2$-hard. The $\Pi_4$ upper bound comes from covering lemmas that replace the quantifiers over uncountably many measures by quantifiers over finite patterns.

## Sources

- Léo Gayral (Léopoldine Gayral in the arXiv copy) and Mathieu Sablik, "Arithmetical Hierarchy of the Besicovitch-Stability of Noisy Tilings", *Theory of Computing Systems* 67(6), 2023, pp. 1209–1240, doi:[10.1007/s00224-023-10142-y](https://doi.org/10.1007/s00224-023-10142-y); read in arXiv:2209.01949v1 ([arXiv](https://arxiv.org/abs/2209.01949v1)), whose numbering is used: Definitions 2.1–2.5 (SFT, noisy SFT, noisy measures, Besicovitch distance, stability) and the definition of $P_{\mathrm{stab}}$ in Section 2, Proposition 3.1 (instability of the red-black Robinson tiling), Corollary 4.2, Theorem 5.1, Proposition 5.7, Theorem 5.11, and Theorem 6.8 (Section 6).
