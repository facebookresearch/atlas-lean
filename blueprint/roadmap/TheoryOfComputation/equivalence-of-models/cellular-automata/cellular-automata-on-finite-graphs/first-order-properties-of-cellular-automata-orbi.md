# First-order properties of cellular automata orbits on finite graphs are undecidable

There is a fixed first-order sentence about cellular automata orbits for which no algorithm decides, given a local rule, whether the rule
satisfies the sentence on some finite graph; and on Cayley graphs of groups that are not virtually free, model checking a fixed sentence is
$\Sigma^1_1$-hard.

**Theorem (Theyssier).** For [cellular automata on labeled graphs and first-order logic on their orbits](cellular-automata-on-labeled-graphs-and-first-or.md):

1. there is a first-order sentence $\phi$ such that it is undecidable, given a CA local rule $f$ as a finite table, whether some finite labeled graph $G$ satisfies $F_{G,f} \models \phi$ (Corollary 4 of the source);
2. for every $D$ there is a first-order sentence $\phi'$ such that, for every Cayley graph $G$ of a finitely generated group with respect to a finite symmetric generating set of at most $D$ elements, the model checking problem
   $\mathcal{CA}(\phi', G)$ is computable if the group is virtually free and $\Sigma^1_1$-hard otherwise (Corollary 3 of the source).

Item 1 is a counterpart, for local interaction rules and dynamical properties, of Trakhtenbrot's theorem. The source also shows that for a fixed $D$ there is a fixed first-order
sentence whose model checking problem on a connected graph of degree at most $D$, typically infinite, is computable exactly when the graph has finite treewidth: it has a tree decomposition, over a possibly infinite tree, whose bags all have at most $k + 1$ vertices for some $k$.

## Depends on

- [Cellular automata on labeled graphs and first-order logic on their orbits](cellular-automata-on-labeled-graphs-and-first-or.md)
- [Cayley digraph](../../../../GraphTheory/algebraic-graph-theory/part-01/directed-cayley-graph.md)
- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem is undecidable by multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Expansion

Both items rest on an effective translation of monadic second-order sentences about labeled graphs into pairs of a first-order sentence on orbits and a local rule, uniformly
enough that a fixed first-order sentence suffices. For item 1, finite rectangular grids, their corners and Turing machine computations written on them as domino colorings are
definable in monadic second-order logic, so a graph satisfying the translated property exists exactly when the machine halts from the empty tape at the rightmost cell it has visited, a variant of the halting problem that is undecidable by a direct transformation of machines (proof of Corollary 4). For item 2, the Cayley graph of a finitely
generated group that is not virtually free contains the infinite grid as a minor (it has a thick end, and Halin's grid theorem applies), and a monadic second-order sentence
over such a minor encodes the recurring domino problem, which is $\Sigma^1_1$-hard (Harel); for virtually free groups, monadic second-order logic is decidable (Muller and Schupp). A good expansion adds and links pages for the halting problem of Turing machines from the empty tape, for Harel's $\Sigma^1_1$-hardness of the recurring domino problem and for the two translations (Theorems 4 and 5 of the source).

## Sources

- G. Theyssier, "FO logic on cellular automata orbits equals MSO logic", in *51st International Colloquium on Automata, Languages, and Programming (ICALP 2024)*, LIPIcs 297, paper 154, 2024, doi:10.4230/LIPIcs.ICALP.2024.154; read in arXiv:2404.16430v1: Corollaries 3 (one fixed FO formula) and 4 (finite graphs) in Section 4 with their proofs and Lemma 11 before them, and Theorems 4 and 5 (the translations) of Section 3, with the numbering of that version (lemmas, theorems and corollaries are numbered separately).
