# Word equations with visibly pushdown constraints are undecidable

Constraining the variables of a single word equation to visibly pushdown languages over a common pushdown alphabet makes satisfiability undecidable. Visibly pushdown constraints subsume regular and length constraints, yet have decidable emptiness and are closed under intersection.

A *pushdown alphabet* is a triple $\tilde\Sigma = (\Sigma_c, \Sigma_i, \Sigma_r)$ of pairwise disjoint alphabets (call, internal and return letters) with union $\Sigma$. A *visibly pushdown automaton* over $\tilde\Sigma$ is a pushdown automaton that pushes a stack symbol on every call letter, pops on every return letter (reading the empty stack without popping), and leaves the stack unchanged on internal letters; it accepts by final state, with no condition on the stack.

There is no algorithm that decides, given a pushdown alphabet $\tilde\Sigma$, a single word equation $E$ over $\Sigma$, and for each variable $x$ of $E$ a visibly pushdown automaton over this same $\tilde\Sigma$ with language $L_x$, whether $E$ has a solution $h$ (variables mapped to possibly empty words over $\Sigma$) with $h(x) \in L_x$ for every $x$.

The pushdown alphabet is part of each instance; the statement is not about every fixed partition. If all letters are internal, visibly pushdown constraints are ordinary regular constraints, and satisfiability is decidable.

## Depends on

- [Word equations with length and regular constraints](length-and-regular-constraints.md)
- [Visibly pushdown automata and visibly pushdown languages](../../context-free-languages/visibly-pushdown-languages/visibly-pushdown-automata.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

- [Closure properties of visibly pushdown languages](../../context-free-languages/visibly-pushdown-languages/closure-properties-of-visibly-pushdown-languages.md)
- [Systems of word equations over at least two letters reduce to one equation](../word-equation-algorithms/satisfiability/system-of-word-equations-to-one-equation.md)
- [The halting problem is recognizable by multi-stack machines](../../computability/halting-problem-and-rice-s-theorem/tm2-recognizable-halting.md)
- [The halting problem is undecidable by multi-stack machines](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Expansion

The result is the source's Corollary 6, derived from its Theorem 5: *every recursively enumerable language $L \subseteq \Sigma_0^*$ over an input alphabet $\Sigma_0$ is expressed by a variable $x$ of a conjunction $\psi$ of word equations and visibly pushdown membership constraints, over a larger alphabet $\Sigma \supseteq \Sigma_0$ with a pushdown partition constructed from the Turing machine, with $L = \{h(x) : h \text{ satisfies } \psi\}$.* Given a one-tape Turing machine $M$ accepting $L$, normalised (left end marker, single accepting state, fixed final head position), the construction encodes accepting computations as words in which configurations are stored in a palindromic way. A visibly pushdown language can check that adjacent stored configurations are related by one step of $M$, since a step changes a configuration only locally and the stack can match symmetric positions. The construction uses word equations to express the offset copy that links one step pair to the next, by introducing variables for concatenations of earlier variables and constants. The input word is then extracted by a word equation.

For the corollary, take the halting set of a fixed input, which is recognizable but not decidable, coded as a language over $\Sigma_0$, and a word $w$: satisfiability of $\psi \wedge x = w$ decides whether $w \in L$, so it is undecidable. The conjunction of word equations becomes a single equation with the same solutions (the reduction of systems to one equation; the extended alphabet has two distinct letters), and several constraints on one variable are merged into one because visibly pushdown languages over a common pushdown alphabet are closed under intersection. Theorem 5's construction is internal to the source.

## Sources

- Joel D. Day, Vijay Ganesh, Nathan Grewal, Matthew Konefal and Florin Manea, "A Closer Look at the Expressive Power of Logics Based on Word Equations", *Theory of Computing Systems* 68:322–379, 2024, <https://doi.org/10.1007/s00224-023-10154-8>, Section 2.3 (pushdown alphabets, visibly pushdown automata, the common partition, Definition 8), Lemma 3 (formulas as one equation), Theorem 5 (every recursively enumerable language is expressible, with the extended alphabet of its construction), Corollary 6 (undecidability, also for a single equation with one visibly pushdown constraint per variable), Remark 6 (only conjunctions are used), Lemma 9 (simulation of length and regular constraints), Section 1 (closure and decidability properties of visibly pushdown languages).
