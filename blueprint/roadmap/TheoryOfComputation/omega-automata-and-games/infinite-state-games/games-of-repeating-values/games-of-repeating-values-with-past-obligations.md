# Games of repeating values with past obligations are undecidable

Deciding whether the system player wins a game of repeating values whose winning condition uses only non-nested past equality obligations is
undecidable, already with one data variable per player and local tests of distance at most three.

Consider [the logic of repeating values and its games](logic-of-repeating-values-and-its-games.md). In the fragment $\mathrm{LRV}[\top, \approx, \leftarrow]$, data values may only be compared by local tests $x \approx \mathsf{X}^j y$ and by
non-nested past equality obligations $x \approx \Diamond^{-1} y$ (the value of $x$ now occurred earlier in $y$), besides Boolean variables and linear temporal logic with past. The *distance* of a local test $x \approx \mathsf{X}^j y$
is $|j|$.

**Theorem.** The winning strategy existence problem for games of repeating values with winning conditions in $\mathrm{LRV}[\top, \approx, \leftarrow]$ is undecidable, even when the formula contains one data variable of the
environment and one data variable of the system, and every local test has distance at most $3$ (Theorem 4.1).

In contrast, the problem becomes decidable when the formula contains no data variable of the environment (*single-sided* games), by a reduction to single-sided games on vector addition systems with states, and
even with nested formulas that use only past modalities. Single-sided games become undecidable when nested formulas may use the future modality $\mathsf{F}$, even without future obligations (Section 8, by Lemma 8.2 from the reset lossy counter machines of Theorem 8.1), and single-sided games with future obligations, $\mathrm{LRV}[\top, \approx, \rightarrow]$, are undecidable too (Theorem 6.1).

## Depends on

- [The logic of repeating values and its games](logic-of-repeating-values-and-its-games.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the reachability problem for two-counter machines. First, with an environment data variable $x$, a system data variable $y$ and Boolean variables of the environment encoding the instructions of
the machine, a formula of the fragment forces the two players to simulate runs of the machine: the value of the first counter before a step is the number of data values that have occurred in $x$ but not yet in $y$, and
symmetrically for the second counter, so that past obligations can detect a wrong zero test. A second step eliminates the Boolean variables by encoding them with local tests between the two data variables at nearby
positions, which needs local tests of distance at most $3$.

## Sources

- D. Figueira, A. Majumdar and M. Praveen, "Playing with repetitions in data words using energy games", *Logical Methods in Computer Science* 16(3), paper 1, 2020, doi:10.23638/LMCS-16(3:1)2020; read in arXiv:1802.07435v7, whose numbering is used here: Theorem 4.1 with its two-step proof (Lemmas 4.2 and 4.3), the decidability results for single-sided games in Sections 5 and 7 (Corollary 5.4), Theorem 6.1 on single-sided future games, and Section 8 (Theorem 8.1 and Lemma 8.2) on single-sided games with nested future formulas.
