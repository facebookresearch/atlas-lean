# Prefix-density is undecidable for one-counter one-reversal languages

It is undecidable whether every word over the alphabet is a prefix of a word accepted by a given nondeterministic one-way one-counter machine whose counter makes at most one reversal.

**Theorem.** It is undecidable, given a machine accepting a language $L \subseteq \Sigma^*$ in $\mathrm{NCM}(1, 1)$, whether $L$ is [prefix-dense](prefix-suffix-and-infix-dense-languages.md), that is, whether $\mathrm{pref}(L) = \Sigma^*$.

For deterministic machines the problem is decidable: prefix-density is decidable for every $\mathrm{DCM}$ language and for every deterministic pushdown language.

## Depends on

- [Reversal-bounded counter machines](reversal-bounded-counter-machines.md)
- [Prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Suffix-density is undecidable for reversal-bounded counter languages](suffix-density-of-counter-languages.md)

## Expansion

Each class $\mathrm{NCM}(k, l)$ is effectively closed under reversal, and $\mathrm{pref}(L^R) = \Sigma^*$ if and only if $\mathrm{suff}(L) = \Sigma^*$. So the undecidability of suffix-density for $\mathrm{NCM}(1, 1)$ transfers to prefix-density.

## Sources

- J. Eremondi, O. H. Ibarra and I. McQuillan, "On the Density of Context-Free and Counter Languages", *International Journal of Foundations of Computer Science* 29(2):233–250, 2018, doi:[10.1142/S0129054118400051](https://doi.org/10.1142/S0129054118400051); numbering of arXiv:1903.03001v1: Corollary 4 (prefix-density of $\mathrm{NCM}(1,1)$) in Section 3 with its proof, and Corollary 2 and Proposition 2 (decidability of prefix-density for $\mathrm{DCM}$ and $\mathrm{DPDA}$ languages) in the same section.
