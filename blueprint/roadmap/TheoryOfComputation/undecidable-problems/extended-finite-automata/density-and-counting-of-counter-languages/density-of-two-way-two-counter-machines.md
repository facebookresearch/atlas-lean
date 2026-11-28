# Density is undecidable for two-way deterministic automata with two reversal-bounded counters

It is undecidable whether the language of a given two-way deterministic finite automaton with two reversal-bounded counters is dense, that is, whether every word is an infix of an accepted word.

Let $2\mathrm{DCM}(2)$ denote the two-way deterministic finite automata with end-markers on both sides of the input, augmented with two reversal-bounded counters, as in [reversal-bounded counter machines](reversal-bounded-counter-machines.md) but with a two-way input head. A language $L \subseteq \Sigma^*$ is *dense* if every word of $\Sigma^*$ is an infix of some word of $L$, as in [prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md).

**Theorem (Ibarra and McQuillan).** It is undecidable, given a $2\mathrm{DCM}(2)$ machine $M$, whether $L(M)$ is dense (Corollary 12).

By contrast, density is decidable for unary two-way nondeterministic finite automata with reversal-bounded counters, since these accept regular languages (Proposition 13); for two-way deterministic automata with one unrestricted counter over a unary alphabet it is undecidable again.

## Depends on

- [Reversal-bounded counter machines](reversal-bounded-counter-machines.md)
- [Prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md)
- [Deterministic two-way automaton](../../../regular-languages/automata-and-expressions/two-way-finite-automata/two-way-dfa.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

If a family of languages has undecidable emptiness and is closed under right marked concatenation with regular languages, density is undecidable for it: for a new letter $\natural$, the language $L\natural(\Sigma \cup \{\natural\})^*$ is dense exactly when $L$ is nonempty (Proposition 7). The family of $2\mathrm{DCM}(2)$ languages has this closure property, and its emptiness problem is undecidable already for machines accepting letter-bounded languages, a result of Ibarra; a good expansion links it.

## Sources

- O. H. Ibarra and I. McQuillan, "On the density of languages accepted by Turing machines and other machine models", *Journal of Automata, Languages and Combinatorics* 23 (2018), pp. 189–199, doi:10.25596/jalc-2018-189; read as arXiv:1903.03018v1, <https://arxiv.org/abs/1903.03018v1>, whose numbering is used here: Proposition 7, Corollary 12 and Proposition 13 with the surrounding paragraphs of Section 3.
