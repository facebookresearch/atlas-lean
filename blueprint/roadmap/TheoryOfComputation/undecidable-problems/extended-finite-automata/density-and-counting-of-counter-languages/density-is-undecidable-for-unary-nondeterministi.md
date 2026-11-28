# Density is undecidable for unary nondeterministic two-pushdown automata with one reversal each

No algorithm decides whether a given unary language, accepted by a real-time nondeterministic automaton with two pushdowns each of
which reverses at most once, is dense.

Over a one-letter alphabet $\{a\}$, a language $L$ is
[dense](prefix-suffix-and-infix-dense-languages.md) exactly when $\mathrm{inf}(L) = a^*$, that is, when $L$ is infinite.

**Theorem.** It is undecidable, given a unary language $L$ accepted by a one-way nondeterministic real-time automaton with two
pushdowns, both $1$-reversal-bounded, whether $L$ is dense.

The source conjectures that density is decidable for unary languages of one-way deterministic two-pushdown automata, so
nondeterminism is used here.

## Depends on

- [Prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md)
- [Pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Density is undecidable for deterministic two-pushdown automata with one reversal each](density-is-undecidable-for-deterministic-two-pus.md)

## Expansion

Start from the real-time deterministic two-pushdown automaton $M_1$ that accepts exactly the encodings of a halting computation of
a deterministic Turing machine $Z$ on the blank tape. The unary automaton $M$ reads one letter $a$ for each move of $M_1$ while
guessing the input of $M_1$; if $M_1$ reaches its accepting state after $a^k$, then $M$ accepts every $a^{k+i}$ with $i \ge 0$.
If $Z$ halts, $\mathrm{inf}(L(M)) = a^*$; otherwise $L(M)$ is empty. So $L(M)$ is dense exactly when $Z$ halts.

## Sources

- O. H. Ibarra and I. McQuillan, "On the density of languages accepted by Turing machines and other machine models", *Journal of Automata, Languages and Combinatorics* 23:189–199, 2018, doi:10.25596/jalc-2018-189; Section 3 of the version arXiv:1903.03018v1: Proposition 11 with its proof, and the conjecture before it.
