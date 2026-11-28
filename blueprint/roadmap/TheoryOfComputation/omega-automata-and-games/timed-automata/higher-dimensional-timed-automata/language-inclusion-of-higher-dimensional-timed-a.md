# Language inclusion of higher-dimensional timed automata is undecidable

No algorithm decides whether the language of one higher-dimensional timed automaton is contained in the language of another.

**Corollary.** Given [higher-dimensional timed automata](higher-dimensional-timed-automata-and-their-lang.md) $A_1$ and $A_2$, it is
undecidable whether $\mathcal{L}(A_1) \subseteq \mathcal{L}(A_2)$ (Corollary 56 of the source).

Both automata are part of the input, with no bound on their dimension. Language inclusion is undecidable already for ordinary timed
automata over finite timed words, which embed into HDTAs; region equivalence, on the other hand, extends to HDTAs and is used in the
source to study the untimings of their languages.

## Depends on

- [Higher-dimensional timed automata and their languages](higher-dimensional-timed-automata-and-their-lang.md)
- [Timed automata over finite timed words](../decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The translation $H$ maps a timed automaton $A$ to an HDTA with $\mathcal{L}(H(A)) = \{i_1(w) : w \in \mathcal{L}(A)\}$, and $i_1$ is injective
and compatible with concatenation. Hence $\mathcal{L}(A_1) \subseteq \mathcal{L}(A_2)$ holds for timed automata exactly when
$\mathcal{L}(H(A_1)) \subseteq \mathcal{L}(H(A_2))$ holds for their translations, and language inclusion of timed automata over finite timed words
is undecidable (Alur and Dill).

## Sources

- A. Amrane, H. Bazille, E. Clement, U. Fahrenberg and P. Schlehuber-Caissier, "Higher-dimensional timed automata for real-time concurrency", in *Design and Verification of Cyber-Physical Systems: From Theory to Applications*, Lecture Notes in Computer Science 16060, pp. 66–100, Springer, 2026, doi:10.1007/978-3-032-16855-9_4; read in arXiv:2401.17444v4: Corollary 56 at the end of Section 8 (From Timed Automata to HDTAs), Theorem 55 (the language of the translation) before it, and Section 9 (region equivalence, Corollary 64).
