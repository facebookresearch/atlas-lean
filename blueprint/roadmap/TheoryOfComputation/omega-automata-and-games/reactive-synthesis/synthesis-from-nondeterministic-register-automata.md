# Register transducer synthesis from nondeterministic register automata is undecidable

No algorithm decides whether a specification given by a nondeterministic register automaton over data words is realized by some register transducer, nor by one with at most $k$ registers for any fixed $k\ge1$.

**Theorem.** For [register transducer synthesis from data-word specifications](register-transducer-synthesis-from-data-word.md):
1. $\mathrm{Real}(\mathrm{NRA},\mathrm{RT})$ is undecidable: no algorithm decides whether a specification given by a nondeterministic parity register automaton is realized by some register transducer;
2. for every fixed $k\ge1$, $\mathrm{Real}(\mathrm{NRA},\mathrm{RT}[k])$ is undecidable.

For deterministic specification automata with input-driven outputs, in which every output transition tests the output datum for equality with some register (so the output datum is the content of a register), unbounded synthesis is decidable (the class $\mathrm{DRA}_{\mathrm{ido}}$ of Definition 3.4 of the source), and the source's bounded-synthesis results for URA specifications and for test-free NRA specifications are decidable as well; the undecidability above comes from nondeterminism with data.

## Depends on

- [Register transducer synthesis from data-word specifications](register-transducer-synthesis-from-data-word.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction is from universality of nondeterministic register automata over finite data words, undecidable by Neven, Schwentick and Vianu. Given such an automaton $A$, the specification $S=S_1\cup S_2\cup T$ reads a finite data word $w$, a separator $\#$, and then: $S_1$ allows outputs that swap the first two labels read after $\#$; $S_2$ allows the identity after $\#$ when $w\in L(A)$; $T$ allows the identity on inputs without $\#$, so the domain is total. Each part, hence $S$, is NRA-definable. If $A$ is universal, the identity, a one-register transducer, realizes $S$. Otherwise, for $w\notin L(A)$ a realizer would have to output the second label after $\#$ before reading it. Since a single register suffices in the positive case, the reduction also proves the bounded statement.

## Sources

- Léo Exibard, Emmanuel Filiot and Pierre-Alain Reynier, "Synthesis of Data Word Transducers", *Logical Methods in Computer Science* 17(1), 2021, paper 22, doi:[10.23638/LMCS-17(1:22)2021](https://doi.org/10.23638/LMCS-17(1:22)2021); numbering of arXiv:1905.03538v5 ([arXiv](https://arxiv.org/abs/1905.03538v5)): Theorem 3.1 and its proof, Theorem 3.2, the decidable subclass of Section 3.2 and the bounded-synthesis results of Section 4.
