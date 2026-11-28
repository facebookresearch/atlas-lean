# Equivalence of copyless tropical cost register automata is undecidable

No algorithm decides whether two copyless cost register automata over the natural numbers with min and addition of constants compute the
same function, nor whether the image of one is semilinear; and no algorithm decides whether a min-plus weighted automaton over the integers is
bounded from above.

**Theorem.** For [copyless cost register automata over the tropical semirings](copyless-cost-register-automata-over-the-tropica.md):

1. (*equivalence*) given two $\mathbb{N}_\infty$-CCRA $\mathcal{C}, \mathcal{C}'$ over $A^*$, it is undecidable whether $\mathcal{C}(w) = \mathcal{C}'(w)$ for all $w \in A^*$;
2. (*semilinearity*) given an $\mathbb{N}_\infty$-CCRA $\mathcal{C}$, it is undecidable whether its image $\mathcal{C}(A^*)$ is semilinear, that is, eventually periodic;
3. (*upper boundedness*) given a weighted automaton $\mathcal{A}$ over $(\mathbb{Z}_\infty, \min, +)$, it is undecidable whether some $c \in \mathbb{Z}$ satisfies $\mathcal{A}(w) \le c$ for all
   $w \in A^*$; here $\infty \le c$ is false, so a word with no accepting run violates every bound, as in the source's statement.

Copyless cost register automata are a weak model, contained in the linearly ambiguous weighted automata. Since these problems are decidable for finitely
ambiguous weighted automata, the source presents them as arguably the simplest generalization of deterministic weighted automata with undecidable
equivalence.

## Depends on

- [Copyless cost register automata over the tropical semirings](copyless-cost-register-automata-over-the-tropica.md)
- [Semilinear set of vectors](../../../../context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)
- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proofs simulate vector addition systems with states and zero tests, whose state reachability is undecidable even when at most one run reaches the
state. Using repeated minima, a copyless automaton checks a run of the counter machine encoded in the input: its output takes a designated minimal value
exactly on encodings of correct runs reaching the target state. Changing the output function to $\min\{r_1 + 1, \dots, r_k + 1\}$ over the check registers changes the
value exactly on correct runs, which gives equivalence. For upper boundedness, the simulating automaton is converted into an equivalent weighted automaton
that outputs $1$ exactly on correct runs and nonpositive values otherwise, and a new letter iterates it, so the iterated automaton is bounded exactly when no
correct run exists.

## Sources

- S. Almagor, M. Cadilhac, F. Mazowiecki and G. A. Pérez, "Weak cost register automata are still powerful", *International Journal of Foundations of Computer Science* 31(6):689–709, 2020, doi:10.1142/S0129054120410026; conference version in *Developments in Language Theory (DLT 2018)*, Lecture Notes in Computer Science 11088, pp. 83–95, 2018, doi:10.1007/978-3-319-98654-8_7. Read in arXiv:1804.06336v1: Theorems 2 (Equivalence), 3 (Semilinearity) and 4 (Upperboundedness) of Section 6 (Applications) with their proofs, Theorem 1 (Simulation) of Section 5, Proposition 1 on vector addition systems with zero tests in Section 2, Proposition 2 of Section 3, and the introduction, with the numbering of that version.
