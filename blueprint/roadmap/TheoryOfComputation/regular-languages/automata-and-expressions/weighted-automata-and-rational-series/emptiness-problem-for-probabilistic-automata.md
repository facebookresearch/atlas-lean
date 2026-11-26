# The emptiness problem for probabilistic automata is undecidable

There is no algorithm that decides, given a [probabilistic automaton](probabilistic-automata-and-cut-point-languages.md) $\mathcal{A}$, whether some word $w$ has
$P_{\mathcal{A}}(w) > \lambda$, for any fixed cut-point $\lambda$ with $0 < \lambda < 1$; the same holds with $P_{\mathcal{A}}(w) \ge \lambda$ (Nasu and Honda; Paz). The first proofs
reduce the Post correspondence problem, and an independent proof reduces the halting problem for two-counter machines (Condon and Lipton).

## Depends on

- [Probabilistic automata and cut-point languages](probabilistic-automata-and-cut-point-languages.md)

## Expansion

This page becomes ready once:

- The reduction from the Post correspondence problem to emptiness of probabilistic automata, from Section 1.4 of the cited paper and the works it cites (proof prerequisite; not yet stated)

## Sources

- G. Rote, "Probabilistic finite automaton emptiness is undecidable for a fixed automaton", *50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025)*, LIPIcs 345, 2025, paper 86, doi:10.4230/LIPIcs.MFCS.2025.86: Section 1.1 (the emptiness problem, undecidable for every fixed cut-point in $(0, 1)$, with $>$ or $\ge$), Section 1.2 (the history of the proofs, crediting Nasu and Honda, Claus, and Condon and Lipton, with the footnote on the attribution to Paz) and Section 1.4.
