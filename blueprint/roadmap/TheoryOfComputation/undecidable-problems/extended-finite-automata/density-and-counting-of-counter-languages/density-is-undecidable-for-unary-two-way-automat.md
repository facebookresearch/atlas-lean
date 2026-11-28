# Density is undecidable for unary two-way automata with one counter

No algorithm decides whether the language of a given two-way deterministic finite automaton with one unrestricted counter, over a
one-letter alphabet, is dense.

**Theorem.** It is undecidable, given a two-way deterministic finite automaton $M$ with end markers and one unrestricted counter,
over a unary input alphabet $\{a\}$, whether $L(M)$ is [dense](prefix-suffix-and-infix-dense-languages.md). Equally, it is
undecidable whether $L(M) = a^*$, and whether $L(M)$ is finite.

By contrast, for two-way nondeterministic automata with finitely many reversal-bounded counters, density is decidable on unary
languages, since such machines can be converted to finite automata (Ibarra, Jiang, Tran and Wang, the source's reference [11]); for two-way deterministic automata with two
reversal-bounded counters density is undecidable in general.

## Depends on

- [Prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md)
- [Deterministic two-way automaton](../../../regular-languages/automata-and-expressions/two-way-finite-automata/two-way-dfa.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Take a machine $Z$ with no input and two unrestricted counters started at zero, which may be assumed to run into an infinite loop
with increasing counter values when it does not halt; whether $Z$ halts is undecidable (Minsky). On input $a^k$, the automaton $M$
simulates $Z$, keeping the first counter in its own counter and the second counter in the position of its head on the unary input.
If the simulation tries to move past the right end marker, $M$ accepts; if $Z$ halts, $M$ rejects. If $Z$ does not halt then
$L(M) = a^*$, and if $Z$ halts then $L(M)$ is finite; so $L(M)$ is dense, equal to $a^*$, or infinite exactly when $Z$ does not halt.

## Sources

- O. H. Ibarra and I. McQuillan, "On the density of languages accepted by Turing machines and other machine models", *Journal of Automata, Languages and Combinatorics* 23:189–199, 2018, doi:10.25596/jalc-2018-189; Section 3 of the version arXiv:1903.03018v1: Proposition 14 and its proof, Corollary 15, and Corollary 12 ($2\mathrm{DCM}(2)$) and Proposition 13 (unary $2\mathrm{NCM}$) before it.
