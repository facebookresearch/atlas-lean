# Density is undecidable for nondeterministic one-counter languages

It is undecidable whether every word over the alphabet is an infix of a word accepted by a given nondeterministic one-way one-counter machine with no bound on counter reversals.

**Theorem.** It is undecidable, given a machine accepting a language $L \subseteq \Sigma^*$ in $\mathrm{NCA}$, whether $L$ is [infix-dense](prefix-suffix-and-infix-dense-languages.md), that is, whether $\mathrm{inf}(L) = \Sigma^*$.

With a reversal bound the problem becomes decidable, even for pushdown automata: infix-density is decidable for languages of one-way nondeterministic reversal-bounded pushdown automata, since the possible pushdown contents in accepting computations form a regular language.

## Depends on

- [Reversal-bounded counter machines](reversal-bounded-counter-machines.md)
- [Prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

With $T$ and $L_{na}$ as for suffix-density (computations of a fixed Turing machine $Z$ on $a^d$ from the initial to the halting configuration, and those among them that contain an error), let $L' = \overline{\Sigma^* T \Sigma^*}\,\big(L_{na}\, \overline{\Sigma^* T \Sigma^*}\big)^*$. An unrestricted counter suffices to check membership in $L_{na}$ for each block, so $L' \in \mathrm{NCA}$. Every word of $\Sigma^*$ factors into blocks from $T$ separated by words without an infix in $T$, and since initial and final states occur only at the ends of words of $T$, a word of $T$ occurring as an infix of a word of $L'$ must be one of its $L_{na}$ blocks. Hence $\mathrm{inf}(L') = \Sigma^*$ if and only if $T \subseteq L_{na}$, that is, if and only if $Z$ does not halt on $a^d$.

## Sources

- J. Eremondi, O. H. Ibarra and I. McQuillan, "On the Density of Context-Free and Counter Languages", *International Journal of Foundations of Computer Science* 29(2):233–250, 2018, doi:[10.1142/S0129054118400051](https://doi.org/10.1142/S0129054118400051); numbering of arXiv:1903.03001v1: Proposition 8 (infix-density of $\mathrm{NCA}$ languages) in Section 3 with its proof, and Proposition 10 (decidability of infix-density for reversal-bounded $\mathrm{NPDA}$ languages) in the same section.
