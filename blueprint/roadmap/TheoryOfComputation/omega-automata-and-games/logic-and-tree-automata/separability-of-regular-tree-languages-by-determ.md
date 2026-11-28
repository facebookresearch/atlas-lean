# Separability of regular tree languages by deterministic tree-walking automata is undecidable

No algorithm decides, given two regular languages of finite trees, whether some deterministic tree-walking automaton accepts every tree of
the first language and rejects every tree of the second.

Trees are finite, sibling-ordered and labeled by a finite ranked alphabet $\Sigma$, each node having as many children as the arity of its label; regular tree languages are those recognized by
[bottom-up finite tree automata](bottom-up-finite-tree-automata.md). A *deterministic tree-walking automaton* has a finite set of states $Q$, an initial state, and for each letter $a$ of arity $n$ a
transition function

$$
\delta_a : Q \times \{\mathrm{root}, 1, \dots, m\} \to \{\mathrm{accept}, \mathrm{reject}\} \cup \big( Q \times \{\mathrm{parent}, 1, \dots, n\} \big),
$$

where $m$ is the maximal arity in $\Sigma$: in state $q$ at a node labeled $a$ that is the root or the $i$-th child of its parent, it accepts, rejects, or moves to the parent or to a child in a new state. It starts in
the initial state at the root and accepts a tree if its run reaches accept. A set $M$ *separates* $L$ from $K$ if $L \subseteq M$ and $M \cap K = \emptyset$.

**Theorem.** It is undecidable, given two regular tree languages $L$ and $K$ by bottom-up tree automata, whether some deterministic tree-walking automaton accepts all trees in $L$ and rejects all trees
in $K$.

Most natural properties of a single regular language are decidable; this is an undecidable property of a pair of regular tree languages. It is close to Kopczyński's theorem that separability of two
visibly pushdown word languages by a regular word language is undecidable.

## Depends on

- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the problem whether two context-free word languages, given by grammars, can be separated by a regular word language, which is undecidable even for deterministic grammars
(Szymanski and Williams). It uses Kopczyński's transformation of grammars into regular tree languages, unchanged. The new ingredient is the
correctness argument for the stronger separating device: a lemma of Bojańczyk and Colcombet on deterministic tree-walking automata, together with rotations of binary terms, shows that a separating tree-walking
automaton yields a regular separator of the word languages, and conversely a regular separator yields a deterministic tree-walking automaton that tests the sequence of leaves read from left to right. A complete expansion links pages for the undecidability of regular separability of context-free languages (Theorem 3.1 as cited in the source) and for the Bojańczyk–Colcombet lemma.

## Sources

- M. Bojańczyk, "It is undecidable if two regular tree languages can be separated by a deterministic tree-walking automaton", *Fundamenta Informaticae* 154(1–4):37–46, 2017, doi:10.3233/FI-2017-1551; read in arXiv:1703.04997v2: Theorem 1.1, stated in Section 1 and proved in Section 3 (Undecidability of separation) with Lemmas 3.2–3.4, the definitions of Section 2, and the cited Theorem 3.1 on regular separability of context-free languages, with the numbering of that version.
