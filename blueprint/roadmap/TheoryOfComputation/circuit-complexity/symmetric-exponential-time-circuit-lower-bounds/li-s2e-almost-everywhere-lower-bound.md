# Li: S2E is not in i.o.-SIZE[2^n/n], giving almost-everywhere bounds for Σ2E ∩ Π2E and ZPE^NP

$\mathrm{S}_2\mathrm{E}\not\subseteq\text{i.o.-}\mathrm{SIZE}[2^n/n]$, where $L\in\text{i.o.-}\mathrm{SIZE}[s(n)]$ means that for infinitely many $n$, $L\cap\{0,1\}^n$ is computed by a circuit of size at most $s(n)$. That is, some $\mathrm{S}_2\mathrm{E}$ language has, for all sufficiently large $n$, no circuit of size $2^n/n$ on inputs of length $n$, with no advice. Consequently $\mathrm{ZPE}^{\mathrm{NP}}\not\subseteq\text{i.o.-}\mathrm{SIZE}[2^n/n]$ and $\Sigma_2\mathrm{E}\cap\Pi_2\mathrm{E}\not\subseteq\text{i.o.-}\mathrm{SIZE}[2^n/n]$. All three statements hold in every relativized world.

## Proof sketch

Apply the everywhere single-valued $\mathrm{FS}_2\mathrm{P}$ algorithm for Avoid to the truth-table map of small circuits on every length; the canonical hard truth tables define an $\mathrm{S}_2\mathrm{E}$ language that is hard on every large length. The corollaries follow from $\mathrm{S}_2\mathrm{E}\subseteq\mathrm{ZPE}^{\mathrm{NP}}\subseteq\Sigma_2\mathrm{E}\cap\Pi_2\mathrm{E}$.

## Depends on

- [Symmetric alternation: the classes S2TIME[T], S2P and S2E](symmetric-alternation-s2p-s2e.md)

## Proof depends on

- [Li: a single-valued FS2P algorithm solves Avoid on every input length](li-single-valued-fs2p-avoid.md)
- [Chen–Hirahara–Ren: S2E/1 requires circuit size 2^n/n, hence so do Σ2E, (Σ2E ∩ Π2E)/1 and ZPE^NP/1](chr-s2e-advice-near-maximum-lower-bound.md)
- [Cai: S2P is contained in ZPP^NP](cai-s2p-subset-zpp-np.md)
- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- Zeyong Li, "Symmetric Exponential Time Requires Near-Maximum Circuit Size: Simplified, Truly Uniform", STOC (2024), arXiv:2310.17762.
