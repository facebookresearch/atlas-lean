# The value-1 problem for probabilistic automata is undecidable

There is no algorithm that decides, given a [probabilistic automaton](probabilistic-automata-and-cut-point-languages.md) $\mathcal{A}$, whether its value
$\sup_w P_{\mathcal{A}}(w)$ equals $1$, that is, whether some words are accepted with probability arbitrarily close to $1$ (Gimbert and Oualhadj); equivalently,
whether the cut-point $1$ is not isolated. The proof turns any automaton $\mathcal{A}$ into an automaton $\mathcal{B}$ that has value $1$ if some word is accepted by
$\mathcal{A}$ with probability above $1/2$, and accepts every word with probability at most $1/2$ otherwise, so emptiness reduces to the value $1$ problem.

## Depends on

- [Probabilistic automata and cut-point languages](probabilistic-automata-and-cut-point-languages.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](emptiness-problem-for-probabilistic-automata.md)

## Sources

- G. Rote, "Probabilistic finite automaton emptiness is undecidable for a fixed automaton", *50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025)*, LIPIcs 345, 2025, paper 86, doi:10.4230/LIPIcs.MFCS.2025.86: Theorem 7 (the gap amplification of Gimbert and Oualhadj) and the paragraph after it (its use to show that the value 1 problem is undecidable).
- N. Fijalkow, H. Gimbert, E. Kelmendi and Y. Oualhadj, "Deciding the value 1 problem for probabilistic leaktight automata", *Logical Methods in Computer Science* 11(2), 2015, arXiv:1504.04136v2: Section 1 (the undecidability of the value 1 problem, crediting Gimbert and Oualhadj, and the conjecture of Bertoni) and Section 1.2, Problem 1.3 and the reformulation by isolated cut-points.
