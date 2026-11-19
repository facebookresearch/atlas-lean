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
