# Density is undecidable for deterministic two-pushdown automata with one reversal each

No algorithm decides whether every word is an infix of a word accepted by a given real-time deterministic automaton with two
pushdowns, each of which changes between pushing and popping at most once.

A language $L \subseteq \Sigma^*$ is *dense*, or infix-dense, if every word of $\Sigma^*$ is an infix of some word of $L$, in the
sense of [prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md).

**Theorem.** It is undecidable, given a one-way real-time (no $\lambda$-transitions) deterministic automaton with two pushdowns,
each $1$-reversal-bounded, whether its language is dense. Consequently, it is undecidable, given a deterministic real-time Turing
machine with a one-way read-only input and two $1$-reversal-bounded worktapes, whether its language is dense.

A pushdown or worktape is *$1$-reversal-bounded* if it switches at most once between increasing and decreasing the size of its
store. By contrast, density is decidable for nondeterministic Turing machines with a one-way input and a single
reversal-bounded worktape, so the boundary lies between one and two reversal-bounded worktapes.

## Depends on

- [Prefix-dense, suffix-dense and infix-dense languages](prefix-suffix-and-infix-dense-languages.md)
- [Pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Emptiness is undecidable for real-time deterministic two-pushdown automata with one reversal per pushdown: for a deterministic
Turing machine started on the blank tape, such an automaton can check that its input has the form
$ID_1 \# ID_3 \# \cdots \# ID_{2k-1} \natural ID_{2k}^R \# \cdots \# ID_4^R \# ID_2^R$ of a halting computation, pushing the odd
configurations on one pushdown and comparing, a construction essentially due to Baker and Book. Any family with undecidable
emptiness that is closed under right-marked concatenation with regular languages has undecidable density: if $L$ is empty then
$L \natural (\Sigma \cup \{\natural\})^*$ is empty and not dense, and if $w \in L$ then every word is an infix of a word of
$w \natural (\Sigma \cup \{\natural\})^*$. A $1$-reversal-bounded worktape simulates a $1$-reversal-bounded pushdown.

## Sources

- O. H. Ibarra and I. McQuillan, "On the density of languages accepted by Turing machines and other machine models", *Journal of Automata, Languages and Combinatorics* 23:189–199, 2018, doi:10.25596/jalc-2018-189; Section 3 of the version arXiv:1903.03018v1: the proposition on families with undecidable emptiness, the construction after it, and the two corollaries on deterministic real-time two-pushdown automata and Turing machines with two $1$-reversal-bounded worktapes; the decidability proposition for a nondeterministic Turing machine with one reversal-bounded worktape.
