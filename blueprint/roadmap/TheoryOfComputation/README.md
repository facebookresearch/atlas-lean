# Theory of Computation

The mathematical study of what can be computed and at what cost: machine models, computability and undecidability, automata and formal languages, and computational complexity.

[NP-completeness](np-completeness/README.md) is the largest field, with over two fifths of the subject's articles. It
starts from the [Cook–Levin theorem](np-completeness/cook-levin/README.md), that SAT is in NP and every problem in NP
reduces to it by a polynomial-time many-one reduction, and establishes NP-completeness problem by problem, from
variants of [satisfiability](np-completeness/satisfiability/README.md) to Hamiltonian cycles, clique, graph coloring
and subset sum. [Complexity classes](complexity-classes/README.md) has Savitch's theorem, the Immerman–Szelepcsényi
theorem $\mathrm{NL} = \mathrm{coNL}$ and Ladner's theorem, and
[hierarchy theorems and barriers](hierarchy-theorems-and-barriers/README.md) has the time hierarchy theorem and the
Baker–Gill–Solovay [oracles](hierarchy-theorems-and-barriers/relativization-and-oracle-separations/README.md) relative
to which P and NP differ or coincide.

In [regular languages](regular-languages/README.md), Kleene's theorem identifies the languages of finite automata with
those of regular expressions, and [minimization](regular-languages/minimization/README.md) rests on the Myhill–Nerode
theorem. [Context-free languages](context-free-languages/README.md) has normal forms, CYK and Earley recognizers, the
equivalence of grammars with [pushdown automata](context-free-languages/grammars-and-pushdown-automata/README.md), and
the pumping and Ogden lemmas, and [decision procedures](decision-procedures/README.md) decide emptiness and
equivalence of finite automata and emptiness of context-free grammars.

[Turing machines](turing-machines/README.md), from single-tape and multi-tape machines to universal ones, compute
exactly the recursive functions ([equivalence of models](equivalence-of-models/README.md)).
[Computability](computability/README.md) has Rice's theorem and the
[undecidability of the halting problem](computability/halting-problem-and-rice-s-theorem/README.md), Kleene's
[recursion theorem](computability/kleene-s-recursion-theorem/README.md) and the
[Busy Beaver](computability/busy-beaver/README.md) value $\Sigma(5) = 4098$, and
[undecidable problems](undecidable-problems/README.md) include the
[Post correspondence problem](undecidable-problems/post-correspondence-problem/README.md) and
[Hilbert's tenth problem](undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/README.md), by the theorem
of Davis, Putnam, Robinson and Matiyasevich that the recursively enumerable sets are the Diophantine ones.

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
- [Boolean circuit complexity](circuit-complexity/README.md)
- [Algebraic complexity](algebraic-complexity/README.md)
- [Descriptive complexity](descriptive-complexity/README.md)
- [Kolmogorov complexity](kolmogorov-complexity/README.md)
- [NP-completeness](np-completeness/README.md)
- [Probabilistically checkable proofs and inapproximability](pcp-and-inapproximability/README.md)
- [Completeness for other complexity classes](completeness-other-classes/README.md)
- [Problems solvable in polynomial time](polynomial-time-problems/README.md)
- [Fine-grained and exponential-time complexity](fine-grained-complexity/README.md)
