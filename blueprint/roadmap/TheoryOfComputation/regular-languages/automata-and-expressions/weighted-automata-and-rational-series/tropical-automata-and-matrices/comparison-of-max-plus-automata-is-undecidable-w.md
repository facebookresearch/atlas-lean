# Comparison of max-plus automata is undecidable with weights ±1

No algorithm decides whether a max-plus automaton computes only nonnegative values, already for two letters and weights $-1$ and $1$, and for
three letters and weights $-1$, $0$ and $1$ when all states are initial and final.

A *max-plus automaton* over an alphabet $\Sigma$ with $d$ states, a [weighted automaton](../weighted-automata-over-a-semiring.md) over the semiring
$(\mathbb{Z} \cup \{-\infty\}, \max, +)$, is a morphism $\mu$ from $\Sigma^+$ to $d \times d$ matrices over $\mathbb{Z} \cup \{-\infty\}$ with an initial row vector $I$ and a final
column vector $F$ with entries in $\{0, -\infty\}$; it computes $f_{\mathcal{A}}(w) = I \mu(w) F$ for nonempty words $w$. The *comparison problem*, written $\mathrm{Pos}_k(S)$ in the source, respectively
$\mathrm{Pos}^d_k(S)$, asks, given a max-plus automaton on a $k$-letter alphabet with weights in $S$, respectively with weights in $S$ and $d$ states, whether
$f_{\mathcal{A}}(w) \ge 0$ for every nonempty word $w$. An instance is given by its finitely many matrices and vectors, the finite weights written as integers in binary.

**Theorem.**

1. $\mathrm{Pos}_2(\{-1, 1\})$ is undecidable (first part of Theorem 1).
2. The restriction of $\mathrm{Pos}_3(\{-1, 0, 1\})$ to automata whose states are all initial and final is undecidable (first part of Theorem 2).

Item 1 follows directly from the two-counter-machine proof of Colcombet. With a bounded number of states instead of bounded weights the problem stays undecidable, by [a separate result](comparison-of-max-plus-automata-with-553-states.md).

## Depends on

- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof embeds two-counter machines started with both counters at $0$ into max-plus automata, following Colcombet, so that the automaton takes a negative value on some word exactly when the
machine halts; weight-$0$ transitions are replaced, after encoding the alphabet, by a transition of weight $-1$ followed by one of weight $1$. For item 2, a reduction from the general case turns an automaton into one with all states initial and final, at the cost of
one more letter and one more state.

## Sources

- L. Daviaud, P. Guillon and G. Merlet, "Comparison of max-plus automata and joint spectral radius of tropical matrices", in *42nd International Symposium on Mathematical Foundations of Computer Science (MFCS 2017)*, LIPIcs 83, paper 19, 2017, doi:10.4230/LIPIcs.MFCS.2017.19; read in arXiv:1612.02647v2: the first parts of Theorems 1 and 2 of Section 3 with the remarks after them, and the definition of max-plus automata in Section 2.2.
