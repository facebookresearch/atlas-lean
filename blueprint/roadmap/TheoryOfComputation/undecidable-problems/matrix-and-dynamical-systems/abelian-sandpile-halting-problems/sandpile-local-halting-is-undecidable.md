# Local halting of periodic-plus-finite sandpiles on ℤ³ is undecidable

No algorithm decides, given a periodic configuration of chips on $\mathbb{Z}^3$ with finitely many chips added, whether the vertex at the origin topples infinitely often in the abelian sandpile process.

**Theorem.** The *p+f local halting problem* for [periodic-plus-finite abelian sandpiles on ℤ³](periodic-plus-finite-abelian-sandpiles-on-z3.md), which asks for a given p+f sandpile whether $N(0) = \infty$, is undecidable (Theorem 4 of the source).

Unlike vertex prediction and global halting, which reduce to the halting problem, the source leaves open whether local halting reduces to the halting problem for Turing machines (the open-problem paragraph after Theorem 4); a priori it reduces to $\Pi^0_2$.

## Depends on

- [Periodic-plus-finite abelian sandpiles on ℤ³](periodic-plus-finite-abelian-sandpiles-on-z3.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting of single-tape Turing machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The fuse circuit simulating a Turing machine is embedded in a background *bomb*: every vertex receives enough chips that a vertex with at least two coordinates zero in its cell has five chips, one with exactly one coordinate zero has four, and every vertex has at least three, and alarm wires connect the final states of the machine to corner vertices. If a corner topples once, induction on the coordinate sum shows that every vertex of $\mathbb{Z}^3$ topples at least once (Lemma 5 of the source), and then every vertex topples infinitely often (Lemma 10 in the appendix). If the machine never halts, the origin never topples. So the origin topples infinitely often exactly when the Turing machine halts.

## Sources

- H. Cairns, "Some Halting Problems for Abelian Sandpiles Are Undecidable in Dimension Three", *SIAM Journal on Discrete Mathematics* 32(4):2636–2666, 2018, doi:[10.1137/16M1091964](https://doi.org/10.1137/16M1091964); numbering of arXiv:1508.00161v2: Theorem 4 (p+f local halting) with its proof, Lemma 5 (the bomb lemma) and the open problem after Theorem 4.
