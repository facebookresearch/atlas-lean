# Comparison of max-plus automata is undecidable with 553 states

No algorithm decides whether a max-plus automaton with six letters and 553 states computes only nonnegative values, when the weights are unbounded integers; with seven letters and 554 states this holds even when all states are initial and final.

A *max-plus automaton* over an alphabet $\Sigma$ with $d$ states, a [weighted automaton](../weighted-automata-over-a-semiring.md) over the semiring
$(\mathbb{Z} \cup \{-\infty\}, \max, +)$, is a morphism $\mu$ from $\Sigma^+$ to $d \times d$ matrices over $\mathbb{Z} \cup \{-\infty\}$ with an initial row vector $I$ and a final
column vector $F$ with entries in $\{0, -\infty\}$; it computes $f_{\mathcal{A}}(w) = I \mu(w) F$ for nonempty words $w$. The problem $\mathrm{Pos}^d_k(S)$ asks, given a max-plus automaton with $d$ states on a $k$-letter alphabet with weights in $S$, whether
$f_{\mathcal{A}}(w) \ge 0$ for every nonempty word $w$. An instance is given by its finitely many matrices and vectors, the finite weights written as integers in binary.

**Theorem.**

1. $\mathrm{Pos}^{553}_6(\mathbb{Z} \cup \{-\infty\})$ is undecidable (second part of Theorem 1).
2. The restriction of $\mathrm{Pos}^{554}_7(\mathbb{Z} \cup \{-\infty\})$ to automata whose states are all initial and final is undecidable (second part of Theorem 2).

The bounded number of states needs unbounded weights: the proof uses weights in $\{-n-1, -2, -1, 0, 1, n-1\}$ for an input number $n$, and with bounded weights and a bounded number of states the problem becomes decidable. With weights $-1$ and $1$ alone and an unbounded number of states the problem is [undecidable as well](comparison-of-max-plus-automata-is-undecidable-w.md).

## Depends on

- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem of a fixed universal two-counter machine started with counters $(n, 0)$. Lemma 6 of the source builds, from a two-counter machine $M$ with $d$ states and a number $n \ge 0$, a max-plus automaton on six letters with weights in $\{-n-1, -2, -1, 0, 1, n-1\}$ and $2d + 27$ states that takes a negative value on some word exactly when $M$ halts from $(n, 0)$; words encode runs as blocks $a^m b^{m'}$ of counter values separated by counter actions, and the weights depending on $n$ check that the first block is $a^n$, that is, that the first counter starts at $n$. The bound 553 comes from a universal two-counter machine with 268 states, which the source cites from Ivanov's thesis. A complete expansion links a page for a universal two-counter machine with 268 states, taking counters $(\delta(M), 0)$ to a halting run exactly when $M$ halts from $(0, 0)$, stated from a refereed source; the [universality of two-counter machines](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md) alone gives no bound on the number of states. Item 2 follows from item 1 by the reduction to automata whose states are all initial and final, at the cost of one more letter and one more state.

## Sources

- L. Daviaud, P. Guillon and G. Merlet, "Comparison of max-plus automata and joint spectral radius of tropical matrices", in *42nd International Symposium on Mathematical Foundations of Computer Science (MFCS 2017)*, LIPIcs 83, paper 19, 2017, doi:10.4230/LIPIcs.MFCS.2017.19; read in arXiv:1612.02647v2: Theorems 1 and 2 of Section 3, the definition of max-plus automata in Section 2.2, and Lemma 6 and the proof of Theorem 1 in Section 5 (the encoding of a universal two-counter machine).
