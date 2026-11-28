# The regular intersection emptiness problem

For a fixed language $P$ of encoded problem instances, the regular intersection emptiness problem of $P$ is the decision problem whose instance is a deterministic finite automaton and whose question is whether the automaton accepts some positive instance of $P$.

Let $P\subseteq\Sigma^*$ be a fixed language, viewed as the set of encoded positive instances of a decision problem. The *regular intersection emptiness problem* of $P$, written $\mathrm{Int}_{\mathrm{Reg}}(P)$, is:

- *given* a deterministic finite automaton $A$ over $\Sigma$, as finite data,
- *decide* whether its [language](../encoded-finite-automata/language.md) meets $P$, that is, whether $L(A)\cap P\neq\emptyset$.

It asks whether a possibly infinite regular set of instances, given compactly by an automaton, contains a positive one. The same problem has been studied as the *regular realizability problem* $RR(P)$ with *filter language* $P$. The answer depends on the encoding of instances: two encodings that are equivalent for the classical problem may give different regular intersection emptiness problems.

For context-free $P$ the problem is decidable, since [emptiness of the intersection of a context-free and a regular language is decidable](../emptiness-of-context-free-and-regular-intersecti/tm2-decidable-inter-eq-zero.md); it is decidable for several NP-complete and even PSPACE-complete problems. For a unary shuffled encoding of string equality, or for the sequential encoding $s\diamond t$ with erasable padding, it is decidable (Theorems 5 and 6 of the source).

## Depends on

- [Language of an encoded DFA](../encoded-finite-automata/language.md)

## Proof depends on

None.

## Sources

- Petra Wolf, "From decidability to undecidability by considering regular sets of instances", *Theoretical Computer Science* 899, 2022, pp. 25–38, doi:[10.1016/j.tcs.2021.11.006](https://doi.org/10.1016/j.tcs.2021.11.006); read in arXiv:1906.08027v2 ([arXiv](https://arxiv.org/abs/1906.08027v2)), whose numbering is used (separate counters for definitions, theorems and corollaries): Definition 1 and Section 1 (the problem and its relation to regular realizability), Theorems 5 and 6.
