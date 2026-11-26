# Li: symmetric exponential time requires near-maximum circuit size almost everywhere

There is a single-valued $\mathrm{FS}_2\mathrm{P}$ algorithm (without advice) that solves $\mathrm{Avoid}$ on **all** input lengths. Consequently

$$
\mathrm{S}_2\mathrm{E} \not\subseteq \mathrm{i.o.}\text{-}\mathrm{SIZE}\bigl[2^n/n\bigr],
$$

and $\Sigma_2\mathrm{E} \cap \Pi_2\mathrm{E}$ and $\mathrm{ZPE}^{\mathrm{NP}}$ have languages of circuit complexity at least $2^n/n$ for all sufficiently large $n$. Moreover there are pseudodeterministic $\mathrm{FZPP}^{\mathrm{NP}}$ constructions, on all lengths, of Ramsey graphs, rigid matrices, pseudorandom generators, two-source extractors, linear codes, hard truth tables and $K^{\mathrm{poly}}$-random strings with near-optimal parameters.

## Proof sketch

Simplify the Chen-Hirahara-Ren algorithm by having the provers argue directly about the computation history of Korten's reduction on a single input length, using a selector that compares the two provers' claimed histories at the first point of discrepancy, which removes the need for the advice bit and the infinitely-often win-win. Each explicit construction follows through Korten's reductions of the construction problem to $\mathrm{Avoid}$.

## Depends on

- [Chen–Hirahara–Ren: S2E/1 requires circuit size 2^n/n, hence so do Σ2E, (Σ2E ∩ Π2E)/1 and ZPE^NP/1](../symmetric-exponential-time-circuit-lower-bounds/chr-s2e-advice-near-maximum-lower-bound.md)
- [Infinitely-often versus almost-everywhere circuit lower bounds](../algorithmic-method-nqp-and-almost-everywhere-bounds/almost-everywhere-lower-bound.md)

## Proof depends on

- [Chen–Hirahara–Ren: S2E/1 requires circuit size 2^n/n, hence so do Σ2E, (Σ2E ∩ Π2E)/1 and ZPE^NP/1](../symmetric-exponential-time-circuit-lower-bounds/chr-s2e-advice-near-maximum-lower-bound.md)
- [Infinitely-often versus almost-everywhere circuit lower bounds](../algorithmic-method-nqp-and-almost-everywhere-bounds/almost-everywhere-lower-bound.md)

## Sources

- Z. Li, "Symmetric exponential time requires near-maximum circuit size: simplified, truly uniform", STOC (2024), arXiv:2310.17762.
- L. Chen, S. Hirahara, H. Ren, "Symmetric exponential time requires near-maximum circuit size", STOC (2024), arXiv:2309.12912.
