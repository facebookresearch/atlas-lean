# The pumping problem for context-free grammars is Π⁰₁-complete

Whether the language of a given context-free grammar satisfies the context-free pumping lemma with a given pumping constant $p$ is undecidable, and complete for $\Pi^0_1$; for languages given by finite automata the question is decidable.

**Pumping with a constant.** A language $L \subseteq \Sigma^*$ *satisfies the context-free pumping lemma with constant* $p \in \mathbb{N}$ if every $z \in L$ with $|z| \ge p$ can be written as $z = uvwxy$ with $u, v, w, x, y \in \Sigma^*$, $|vx| \ge 1$ and $|vwx| \le p$, such that $u v^t w x^t y \in L$ for every $t \ge 0$. Every [context-free language](../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md) satisfies it for some $p$ (the Bar-Hillel pumping lemma, in this one-constant form).

**Theorem (Gruber, Holzer and Rauch).** The *pumping problem* for context-free grammars, which asks, given a context-free grammar $G$ and a natural number $p$, whether $L(G)$ satisfies the context-free pumping lemma with constant $p$, is undecidable; it is [$\Pi^0_1$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)-complete under many-one reductions. It remains undecidable for linear context-free grammars with the pumping lemma for linear context-free languages.

The constant $p$ is part of the input. When the language is given by a finite automaton, the pumping problem for this lemma is decidable (Theorem 7 of the source).

## Depends on

- [Context-free languages](../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)
- [The arithmetical class $\Pi_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Pumping lemma for context-free languages](../../context-free-languages/closure-and-pumping/pumping-lemma-for-context-free-languages/pumping.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Hardness is a many-one reduction from the emptiness problem for Turing machines. For a machine $M$, the set $\mathrm{INVAL}(M)$ of strings that are not valid accepting computations of $M$ is context-free, and it is all of $\Sigma^*$ exactly when $L(M) = \varnothing$. With a regular language $T_p$ whose minimal pumping constant is $p$, a homomorphism $h$ doubling every letter and a new symbol $\#$, the language $L_M = h(\Sigma^*) \# T_p \cup h(\mathrm{INVAL}(M)) \# \Sigma^+ \cup \Sigma^* \# \cup \#^*$ is context-free and its grammar $G_M$ is computable from $M$; $L_M$ satisfies the lemma with constant $1$ exactly when $L(M) = \varnothing$. The problem lies in $\Pi^0_1$ because negative instances can be recognized: a machine guesses a word $z \in L(G)$ with $|z| \ge p$, checks membership with the CYK algorithm, and for each of the finitely many admissible decompositions $z = uvwxy$ searches for an exponent $t$ with $u v^t w x^t y \notin L(G)$.

## Sources

- H. Gruber, M. Holzer and C. Rauch, "The pumping lemma for context-free languages is undecidable", in *Developments in Language Theory (DLT 2024)*, Lecture Notes in Computer Science 14791, Springer, 2024, pp. 141–155, doi:10.1007/978-3-031-66159-4_11; read in the authors' copy at <http://www.hermann-gruber.com/pdf/dlt-2024.pdf>: Lemma 1 (the context-free pumping lemma), Theorem 11 (undecidability, also for linear grammars), Lemma 13, Lemma 14 and Theorem 15 ($\Pi^0_1$-completeness), Theorem 7 (decidability for finite automata) and Table 1, in the numbering of that copy.
