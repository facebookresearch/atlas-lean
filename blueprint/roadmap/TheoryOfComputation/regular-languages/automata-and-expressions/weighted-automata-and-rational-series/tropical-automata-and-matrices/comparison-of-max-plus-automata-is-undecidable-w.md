# Comparison of max-plus automata is undecidable with 553 states or with weights ±1

No algorithm decides whether a max-plus automaton computes only nonnegative values, already for two letters and weights $-1$ and $1$, or for
six letters and 553 states, and also when all states are initial and final.

A *max-plus automaton* over an alphabet $\Sigma$ with $d$ states, a [weighted automaton](../weighted-automata-over-a-semiring.md) over the semiring
$(\mathbb{Z} \cup \{-\infty\}, \max, +)$, is a morphism $\mu$ from $\Sigma^+$ to $d \times d$ matrices over $\mathbb{Z} \cup \{-\infty\}$ with an initial row vector $I$ and a final
column vector $F$ with entries in $\{0, -\infty\}$; it computes $f_{\mathcal{A}}(w) = I \mu(w) F$ for nonempty words $w$. The *comparison problem* $\mathrm{Comp}_k(S)$, respectively
$\mathrm{Comp}^d_k(S)$, asks, given a max-plus automaton on a $k$-letter alphabet with weights in $S$, respectively with weights in $S$ and $d$ states, whether
$f_{\mathcal{A}}(w) \ge 0$ for every nonempty word $w$.

**Theorem.**

1. $\mathrm{Comp}_2(\{-1, 1\})$ and $\mathrm{Comp}^{553}_6(\mathbb{Z} \cup \{-\infty\})$ are undecidable.
2. The restrictions of $\mathrm{Comp}_3(\{-1, 0, 1\})$ and of $\mathrm{Comp}^{554}_7(\mathbb{Z} \cup \{-\infty\})$ to automata whose states are all initial and final are undecidable.

The first part of item 1 follows directly from the two-counter-machine proof of
Colcombet; the bounded number of states in the second part needs unbounded weights, since with bounded weights and a bounded number of states the problem
becomes decidable.

## Depends on

- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)

## Proof depends on

- [Two-counter machines are universal](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof embeds two-counter machines into max-plus automata, following Colcombet, so that the automaton takes a negative value on some word exactly when the
machine halts. For the bounded number of states, the construction
also simulates the machine on an arbitrary initial counter value $n$, encoded by a widget with two edges of weights $n$ and $-n$, and reduces the halting problem of
a universal two-counter machine. For item 2, a reduction from the general case turns an automaton into one with all states initial and final, at the cost of
one more letter and one more state.

## Sources

- L. Daviaud, P. Guillon and G. Merlet, "Comparison of max-plus automata and joint spectral radius of tropical matrices", in *42nd International Symposium on Mathematical Foundations of Computer Science (MFCS 2017)*, LIPIcs 83, paper 19, 2017, doi:10.4230/LIPIcs.MFCS.2017.19; read in arXiv:1612.02647v2: Theorems 1 and 2 of Section 3, the definition of max-plus automata in Section 2.2 and the encoding of two-counter machines in Section 5.
