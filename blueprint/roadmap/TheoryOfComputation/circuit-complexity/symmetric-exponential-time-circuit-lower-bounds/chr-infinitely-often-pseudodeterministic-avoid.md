# Chen–Hirahara–Ren: an infinitely-often single-valued FZPP^NP/1 algorithm for Avoid

Unconditionally there is a zero-error pseudodeterministic algorithm with an $\mathrm{NP}$ oracle and one bit of advice ($\mathrm{FZPP}^{\mathrm{NP}}/_1$), equivalently a single-valued $\mathrm{FS}_2\mathrm{P}/_1$ algorithm, that solves Avoid on circuits $C\colon\{0,1\}^n\to\{0,1\}^{n+1}$ for infinitely many $n$. It yields unconditional infinitely-often pseudodeterministic $\mathrm{FZPP}^{\mathrm{NP}}/_1$ constructions, with nearly optimal parameters, of Ramsey graphs, rigid matrices, two-source extractors, linear codes and $\mathrm{K}^{\mathrm{poly}}$-random strings. The proofs relativize.

## Proof sketch

The two ingredients are Korten's $\mathrm{P}^{\mathrm{NP}}$ reduction from Avoid to hard truth tables and the iterative win-win paradigm of Chen–Lu–Oliveira–Ren–Santhanam. Within a long interval of input lengths, either the history of Korten's reduction at some length is itself the output of a fully assigned GGM tree of smaller size, giving a short description that symmetric provers can exchange, or one moves to the next length with a smaller hard truth table; some length in the interval must succeed, and the advice bit marks it.

## Depends on

- [Single-valued FΣ2P and FS2P algorithms for search problems](single-valued-fsigma2p-and-fs2p.md)
- [Pseudodeterministic constructions for dense properties, everywhere and infinitely often](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/pseudodeterministic-algorithms/pseudodeterministic-construction-of-dense-property.md)

## Proof depends on

- [Korten's reduction: from a non-image of the GGM tree, an NP oracle finds a non-image of C](korten-reduction-ggm-tree.md)
- [Bootstrapping win-win: recursive hitting sets over lengths n_{i+1} = n_i^β](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/pseudodeterministic-algorithms/bootstrapping-recursive-hitting-sets.md)

## Sources

- Lijie Chen, Shuichi Hirahara and Hanlin Ren, "Symmetric Exponential Time Requires Near-Maximum Circuit Size", STOC (2024), arXiv:2309.12912.
