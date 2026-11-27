# Zero isolation for copyless cost register automata is undecidable

No algorithm decides whether the values of a copyless cost register automaton over the nonnegative rationals stay above some positive constant, although for copyless linear automata boundedness is decidable.

**Theorem.** The zero isolation problem for [copyless cost register automata](copyless-cost-register-automata.md) over $(\mathbb Q_{\ge0},+,\cdot)$ is undecidable: there is no algorithm that, given such an automaton $\mathcal B$, decides whether there is a rational $c>0$ with $\mathcal B(w)\ge c$ for all words $w$.

In contrast, the source shows that zero isolation is decidable, assuming Schanuel's conjecture, for stateless copyless linear automata with three registers in which every update has the form $x\leftarrow c\odot x\oplus d$, so that registers do not interact.

## Depends on

- [Copyless cost register automata](copyless-cost-register-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

First, the $<$-threshold problem (is $\mathcal A(w)<C$ for some $w$?) reduces to zero isolation: a fresh letter $\#$ and a register $z$, updated copylessly by $z\leftarrow\frac1C\,z\cdot\sum_xF(q,x)\,x$ when $\#$ is read while the other registers are reset, give $\mathcal B(w_1\#\cdots\#w_n\#)=\prod_i\mathcal A(w_i)/C$, which tends to $0$ along $(w\#)^i$ iff some $\mathcal A(w)<C$. Second, the halting problem for deterministic two-counter machines reduces to the $<$-threshold problem: words encode candidate runs, and a copyless automaton outputs $0.9$ on encodings of halting runs and at least $1.1$ on all other words, its error tests being implemented by multiplicative copyless gadgets rather than by extra runs as for weighted automata (adapting a proof of Daviaud, Jurdziński, Lazić, Mazowiecki, Pérez and Worrell).

## Sources

- Wojciech Czerwiński, Engel Lefaucheux, Filip Mazowiecki, David Purser and Markus A. Whiteland, "The boundedness and zero isolation problems for weighted automata over nonnegative rationals", in *Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, pp. 1–13, doi:[10.1145/3531130.3533336](https://doi.org/10.1145/3531130.3533336); read in arXiv:2205.13516v1 ([arXiv](https://arxiv.org/abs/2205.13516v1)), cited by section and statement because its theorem counter is not recoverable: the main theorem of Section 3 (its second sentence) and the appendix section showing that zero isolation for copyless CRA is undecidable, with its two lemmas.
