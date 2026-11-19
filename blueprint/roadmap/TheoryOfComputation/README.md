# Theory of Computation

The mathematical study of what can be computed and at what cost: machine models, computability and undecidability, automata and formal languages, and computational complexity.

The theory of NP-completeness
starts from the Cook–Levin theorem, that SAT is in NP and every problem in NP
reduces to it by a polynomial-time many-one reduction, and establishes NP-completeness problem by problem, from
variants of satisfiability to Hamiltonian cycles, clique, graph coloring
and subset sum. Complexity classes has Savitch's theorem, the Immerman–Szelepcsényi
theorem $\mathrm{NL} = \mathrm{coNL}$ and Ladner's theorem, and
hierarchy theorems and barriers has the time hierarchy theorem and the
Baker–Gill–Solovay oracles relative
to which P and NP differ or coincide.

In regular languages, Kleene's theorem identifies the languages of finite automata with
those of regular expressions, and minimization rests on the Myhill–Nerode
theorem. Context-free languages has normal forms, CYK and Earley recognizers, the
equivalence of grammars with pushdown automata, and
the pumping and Ogden lemmas, and decision procedures decide emptiness and
equivalence of finite automata and emptiness of context-free grammars.

[Turing machines](turing-machines/README.md), from single-tape and multi-tape machines to universal ones, compute
exactly the recursive functions (equivalence of models).
Computability has Rice's theorem and the
undecidability of the halting problem, Kleene's
recursion theorem and the
Busy Beaver value $\Sigma(5) = 4098$, and
undecidable problems include the
Post correspondence problem and
Hilbert's tenth problem, by the theorem
of Davis, Putnam, Robinson and Matiyasevich that the recursively enumerable sets are the Diophantine ones.

Communication complexity studies Yao's two-party model:
equality of $n$-bit strings needs $n + 1$ bits deterministically, by the fooling-set and rank
lower bounds, but only a constant number with shared random bits, and
Yao's minimax principle
turns lower bounds against a fixed input distribution into lower bounds for randomized
algorithms.

- [Turing machines](turing-machines/README.md)
- [Equivalence of models of computation](equivalence-of-models/README.md)
- [Computability and undecidability](computability/README.md)
- [Degrees of unsolvability and the arithmetical hierarchy](degrees-and-hierarchies/README.md)
- [Undecidable problems](undecidable-problems/README.md)
- [Decision procedures for automata, grammars and strings](decision-procedures/README.md)
- [Finite automata and regular languages](regular-languages/README.md)
- [Automata on infinite words and infinite games](omega-automata-and-games/README.md)
- [Context-free languages](context-free-languages/README.md)
- [Context-sensitive languages](context-sensitive-languages/README.md)
- [Complexity classes](complexity-classes/README.md)
- [Hierarchy theorems and proof barriers](hierarchy-theorems-and-barriers/README.md)
- [Randomized, interactive and quantum complexity](randomized-and-quantum-complexity/README.md)
- [Counting complexity](counting-complexity/README.md)
- [Pseudorandomness and one-way functions](pseudorandomness-and-one-way-functions/README.md)
- [Communication complexity](communication-complexity/README.md)
- [Boolean circuit complexity](circuit-complexity/README.md)
- [Algebraic complexity](algebraic-complexity/README.md)
- [Descriptive complexity](descriptive-complexity/README.md)
- [Kolmogorov complexity](kolmogorov-complexity/README.md)
- [NP-completeness](np-completeness/README.md)
- [Probabilistically checkable proofs and inapproximability](pcp-and-inapproximability/README.md)
- [Completeness for other complexity classes](completeness-other-classes/README.md)
- [Problems solvable in polynomial time](polynomial-time-problems/README.md)
- [Fine-grained and exponential-time complexity](fine-grained-complexity/README.md)
