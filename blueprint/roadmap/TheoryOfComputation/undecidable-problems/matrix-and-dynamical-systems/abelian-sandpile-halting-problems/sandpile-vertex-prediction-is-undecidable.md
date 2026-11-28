# Vertex prediction for periodic-plus-finite sandpiles on ℤ³ is undecidable

No algorithm decides, given a periodic configuration of chips on $\mathbb{Z}^3$ with finitely many chips added, whether the vertex at the origin ever topples in the abelian sandpile process.

**Theorem.** The *p+f vertex prediction problem* for [periodic-plus-finite abelian sandpiles on ℤ³](periodic-plus-finite-abelian-sandpiles-on-z3.md), which asks for a given p+f sandpile whether the origin topples at least once, is undecidable.

The problem is recursively enumerable, since a machine can simulate the sandpile and stop when the origin topples (the open-problem paragraph after Theorem 4 of the source; by the abelian property, the origin topples in some legal toppling sequence iff $N(0) \ge 1$); the source also notes that with a universal Turing machine the periodic part can be fixed once and for all, so that the problem stays undecidable when only the finitely many added chips are the input.

## Depends on

- [Periodic-plus-finite abelian sandpiles on ℤ³](periodic-plus-finite-abelian-sandpiles-on-z3.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting of single-tape Turing machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Moore and Nilsson showed how to embed wires, AND gates and OR gates in sandpiles of dimension at least two; in dimension three, wires can also cross. Using such one-shot *fuse circuits*, the source builds a periodic sandpile that simulates a Turing machine: one cell of the periodic pattern per tape square and time step, with the third dimension used only to let wires cross, and the finitely many added chips encoding the initial tape. Alarm wires in every cube, linked to each other and translated so that one passes through the origin, fire exactly when the machine enters a final state. Hence the origin topples if and only if the simulated machine halts, and a decision procedure for vertex prediction would decide the halting problem.

## Sources

- H. Cairns, "Some Halting Problems for Abelian Sandpiles Are Undecidable in Dimension Three", *SIAM Journal on Discrete Mathematics* 32(4):2636–2666, 2018, doi:[10.1137/16M1091964](https://doi.org/10.1137/16M1091964); numbering of arXiv:1508.00161v2: Theorem 2 (p+f vertex prediction) with its proof, the construction of fuse circuits simulating a Turing machine before it, and the remarks on fixing the periodic part and on reducibility to the halting problem.
