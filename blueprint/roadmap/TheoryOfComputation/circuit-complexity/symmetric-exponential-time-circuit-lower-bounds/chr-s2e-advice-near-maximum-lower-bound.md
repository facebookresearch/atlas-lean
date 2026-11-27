# Chen–Hirahara–Ren: S2E/1 requires circuit size 2^n/n, hence so do Σ2E, (Σ2E ∩ Π2E)/1 and ZPE^NP/1

There is a language in $\mathrm{S}_2\mathrm{E}/_1$ whose circuit complexity is at least $2^n/n$ (for infinitely many $n$). Consequently $\Sigma_2\mathrm{E}$, $(\Sigma_2\mathrm{E}\cap\Pi_2\mathrm{E})/_1$ and $\mathrm{ZPE}^{\mathrm{NP}}/_1$ each contain a language of circuit complexity at least $2^n/n$. Previously only half-exponential lower bounds were known for these classes, and the smallest class known to require exponential circuit size was $\Delta_3\mathrm{E}=\mathrm{E}^{\Sigma_2\mathrm{P}}$. The result relativizes.

## Proof sketch

Apply the infinitely-often single-valued algorithm for Avoid to the truth-table map of circuits of size $2^n/n$ on $n$ inputs, which has stretch. Its canonical output on length $2^n$ is a truth table of high circuit complexity; defining $L\cap\{0,1\}^n$ to be that truth table gives an $\mathrm{S}_2\mathrm{E}/_1$ language, since each bit of the canonical output is decided by symmetric provers in time $2^{O(n)}$. The bounds for $\mathrm{ZPE}^{\mathrm{NP}}/_1$ and $(\Sigma_2\mathrm{E}\cap\Pi_2\mathrm{E})/_1$ follow from $\mathrm{S}_2\mathrm{E}\subseteq\mathrm{ZPE}^{\mathrm{NP}}\subseteq\Sigma_2\mathrm{E}\cap\Pi_2\mathrm{E}$, and for $\Sigma_2\mathrm{E}$ the advice bit is eliminated.

## Depends on

- [Symmetric alternation: the classes S2TIME[T], S2P and S2E](symmetric-alternation-s2p-s2e.md)

## Proof depends on

- [Chen–Hirahara–Ren: an infinitely-often single-valued FZPP^NP/1 algorithm for Avoid](chr-infinitely-often-pseudodeterministic-avoid.md)
- [Miltersen–Vinodchandran–Watanabe: E^Σ2P contains a language of circuit complexity at least 2^n/n](delta3e-near-maximum-circuit-lower-bound.md)
- [Shannon: most Boolean functions need exponential circuits](../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)
- [Cai: S2P is contained in ZPP^NP](cai-s2p-subset-zpp-np.md)

## Sources

- Lijie Chen, Shuichi Hirahara and Hanlin Ren, "Symmetric Exponential Time Requires Near-Maximum Circuit Size", STOC (2024), arXiv:2309.12912.
