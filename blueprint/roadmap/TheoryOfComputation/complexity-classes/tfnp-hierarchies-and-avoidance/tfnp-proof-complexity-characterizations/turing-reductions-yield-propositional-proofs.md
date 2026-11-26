# Buss–Johnson: Turing reductions between TFNP problems yield Frege and Nullstellensatz proofs, and conversely

If a TFNP problem $Q_1$ is polynomial-time Turing reducible to a TFNP problem $Q_2$ (with circuits given as oracles), then the combinatorial principle asserting totality of $Q_1$ has quasipolynomial-size, polylogarithmic-height, constant-depth, free-cut-free Frege proofs from instances of the principle of $Q_2$, and Nullstellensatz derivations of polylogarithmic degree. Conversely, a family of quasipolynomial-size, polylogarithmic-depth propositional proofs based on decision-tree substitutions yields a polynomial-time Turing reduction, so the construction is optimal. As a corollary, PLS-complete problems are not polynomial-time Turing reducible to PPA problems relative to a generic oracle. Buss and Johnson also show that PLS, PPAD, PPADS and PPA are closed under polynomial-time Turing reductions (this is open for PPP), and introduce the operator $\mathsf M_0\,\&\,\mathsf M_1$ combining two classes, used for modular classes.

## Proof sketch

Unfold the oracle Turing machine into a decision tree of polylogarithmic height whose internal nodes are queries to the input and to the $Q_2$ oracle; each oracle call is answered by an instance of the $Q_2$ principle whose variables are substituted by low-depth decision trees, and the correctness of each path becomes a constant-depth proof of polylogarithmic height. The Nullstellensatz version linearises the same tree. The PLS versus PPA corollary combines the Nullstellensatz direction with known Nullstellensatz degree lower bounds for a PLS-complete principle, which persist relative to a generic oracle.

## Depends on

- [The false-clause search problem S(F) of an unsatisfiable CNF and its universality for TFNP^dt](false-clause-search-problem.md)
- [Cook–Reckhow propositional proof systems](../../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

- [Göös–Kamath–Robere–Sokolov: PPA^dt is characterized by Nullstellensatz degree over F2](ppa-dt-characterized-by-f2-nullstellensatz.md)

## Sources

- Samuel R. Buss and Alan S. Johnson, "Propositional Proofs and Reductions between NP Search Problems", Annals of Pure and Applied Logic 163(9) (2012).
- Mika Göös, Pritish Kamath, Katerina Sotiraki and Manolis Zampetakis, "On the Complexity of Modulo-q Arguments and the Chevalley–Warning Theorem", CCC (2020), arXiv:1912.04467.
