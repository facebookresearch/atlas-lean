# Synthesis of rational resynchronizers for one-way transducers is undecidable

No algorithm decides, given two real-time one-way transducers, whether some rational resynchronizer makes the origin semantics of the first contained in the resynchronized origin semantics of the second; this holds even when the first transducer is functional and the output alphabet is unary.

**Definitions.** Let $T_1, T_2$ be one-way nondeterministic transducers from $\Sigma^*$ to $\Gamma^*$, with $\Sigma$ and $\Gamma$ disjoint. In the [origin semantics](origin-semantics-of-transducers-and-bounded-regu.md), a successful run on input $u$ yields an origin graph: the output word with each output position tagged by the input position that produced it. For one-way transducers an origin graph is the same as a *synchronized word* over $\Sigma \uplus \Gamma$, obtained by writing after each input letter the output word produced while reading it. A *resynchronization* is a relation between origin graphs with the same input and the same output word; for a set $S$ of origin graphs, $R(S)$ is the set of graphs $G'$ with $(G, G') \in R$ for some $G \in S$. A *rational resynchronizer* is a one-way transducer over $\Sigma \uplus \Gamma$ that preserves the projections of synchronized words onto $\Sigma$ and onto $\Gamma$. Write $T_1 \subseteq_o S$ if every origin graph of $T_1$ lies in $S$. A transducer is *real-time* if it produces a bounded amount of output for each input letter it consumes. The *synthesis problem for rational resynchronizers* asks, given $T_1$ and $T_2$, whether $T_1 \subseteq_o R(T_2)$ for some rational resynchronizer $R$.

**Theorem.** Synthesis of rational resynchronizers is undecidable for real-time one-way transducers, even when $T_1$ is functional (Corollary 14 of the source).

The reduction produces instances with a unary output alphabet. The question lies between classical containment $[\![T_1]\!] \subseteq [\![T_2]\!]$ of one-way transducers, which is undecidable, and origin containment $T_1 \subseteq_o T_2$, which is decidable. By contrast, synthesis of rational resynchronizers is decidable when both transducers are functional, and more generally finite-valued.

## Depends on

- [Origin semantics of transducers and bounded regular resynchronizers](origin-semantics-of-transducers-and-bounded-regu.md)
- [Rational relations and transducers](../rational-relations-and-transducers.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The source shows that, for real-time one-way transducers with unary output alphabet, synthesis is inter-reducible with *language-boundedness* of one-counter automata: given a one-counter automaton $A$ over $\Omega$ with $L(A) = \Omega^*$, is there a bound $k$ such that every word is accepted by a run whose counter never exceeds $k$? From $A$ one builds $T_1$, which outputs one letter $c$ per input letter (real-time and functional), and $T_2$, which guesses a run of $A$ and outputs $cc$ on increments, nothing on decrements and $c$ otherwise. If $A$ is bounded by $k$, a resynchronizer simulating a counter in $[-k, k]$ moves the origins of $T_2$ to those of $T_1$; conversely, by a result of Filiot, Jecker, Löding and Winter (bounded-delay resynchronizers suffice for real-time transducers, Theorem 11 of the source) one may assume a resynchronizer of bounded delay, which yields a bound for $A$. Language-boundedness of one-counter automata is undecidable by a reduction, due to Hofman and proved in the source, from the boundedness problem for Minsky machines; a good expansion links pages for both results.

## Sources

- S. Bose, S. N. Krishna, A. Muscholl, V. Penelle and G. Puppis, "On Synthesis of Resynchronizers for Transducers", in *44th International Symposium on Mathematical Foundations of Computer Science (MFCS 2019)*, LIPIcs 138, paper 69, pp. 69:1–69:14, 2019, doi:[10.4230/LIPIcs.MFCS.2019.69](https://doi.org/10.4230/LIPIcs.MFCS.2019.69). Read in arXiv:1906.08688v2 ([arXiv](https://arxiv.org/abs/1906.08688v2)), whose numbering is used here: Section 2 (transducers, origin semantics and synchronized words), Section 3 (resynchronizations and rational resynchronizers), Theorem 7 (functional case), Proposition 12, Theorem 13 and Corollary 14.
