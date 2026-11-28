# Emptiness and containment of linearly ambiguous probabilistic automata are undecidable

No algorithm decides whether a probabilistic automaton whose number of accepting runs grows at most linearly in the word length accepts some word with probability greater than $1/2$, nor whether one such automaton is contained in another; for finitely ambiguous automata emptiness is decidable.

**Probabilistic automata and ambiguity.** A *probabilistic automaton* $\mathcal{A} = (\Sigma, Q, \delta, \iota, F)$ has a finite alphabet $\Sigma$, a finite set $Q$ of states, a transition function $\delta$ assigning to each state and letter a distribution on $Q$ (nonnegative rationals with sum at most $1$), an initial distribution $\iota$ on $Q$ and a set $F \subseteq Q$ of final states. A run over $a_1 \cdots a_n$ is a sequence of transitions $(q_{i-1}, a_i, q_i)$ of positive probability; it is accepting if $\iota(q_0) > 0$ and $q_n \in F$, and its probability is $\iota(q_0) \prod_i \delta(q_{i-1}, a_i, q_i)$. The automaton maps each word $w$ to the sum $\mathcal{A}(w)$ of the probabilities of its accepting runs on $w$. It is *finitely ambiguous* if some $k$ bounds the number of accepting runs on every word, and *linearly ambiguous* if some polynomial $P$ of degree at most $1$ bounds the number of accepting runs on every word $w$ by $P(|w|)$.

This differs from the model of [probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md) in two conventions of the source: transition rows and the initial distribution may sum to less than $1$, and the start is an initial distribution rather than a single state; all entries are rational, so an instance is a finite table. The *emptiness problem* asks, given $\mathcal{A}$, whether some word $w$ has $\mathcal{A}(w) > \frac12$. The *containment problem* asks, given $\mathcal{A}$ and $\mathcal{B}$, whether $\mathcal{A}(w) \le \mathcal{B}(w)$ for all words $w$.

**Theorem (Daviaud, Jurdziński, Lazić, Mazowiecki, Pérez and Worrell).** The emptiness and containment problems are undecidable for the class of linearly ambiguous probabilistic automata.

This strengthens undecidability for quadratically ambiguous automata (Fijalkow, Riveros and Worrell). It is optimal for emptiness, which is decidable for finitely ambiguous automata; the same paper shows that the gap version of emptiness is decidable for polynomially ambiguous automata.

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces the halting problem for two-counter machines, undecidable because such machines simulate Turing machines, through a more general proposition about pairs of linearly ambiguous automata; the reduction resembles the one used for the comparison problem of max-plus automata. Containment generalizes emptiness.

## Sources

- L. Daviaud, M. Jurdziński, R. Lazić, F. Mazowiecki, G. A. Pérez and J. Worrell, "When are emptiness and containment decidable for probabilistic automata?", *Journal of Computer and System Sciences* 119 (2021), pp. 78–96, doi:10.1016/j.jcss.2021.01.006; conference version "When is Containment Decidable for Probabilistic Automata?", *ICALP 2018*, LIPIcs 107, paper 121, doi:10.4230/LIPIcs.ICALP.2018.121; read as arXiv:1804.09077v4, <https://arxiv.org/abs/1804.09077v4>: Theorem 2 (undecidability for linearly ambiguous automata) with its proof in the section on undecidability for linearly ambiguous automata, the definitions of probabilistic automata and ambiguity in Section 2.1, and the introduction (emptiness with threshold $\frac12$, containment, the quadratic and finitely ambiguous cases) and Theorem 1 (gap emptiness for polynomially ambiguous automata), in the numbering of that version.
