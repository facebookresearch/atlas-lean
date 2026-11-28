# Periodic-plus-finite abelian sandpiles on ℤ³

On the cubic lattice $\mathbb{Z}^3$ a vertex with at least six chips may topple, sending one chip to each neighbor. A periodic-plus-finite sandpile starts from a configuration that is periodic in all three coordinates with finitely many chips added; it is a finite object, and the number of topplings at each vertex does not depend on the order of moves.

**Definition.** Consider $\mathbb{Z}^3$ as a graph in which $v$ and $w$ are adjacent when $\lVert v - w \rVert_1 = 1$, so every vertex has degree $6$. A *configuration* is a map $S : \mathbb{Z}^3 \to \mathbb{Z}$ giving the number of chips on each vertex. A vertex $v$ is called *unstable* if it has at least $6$ chips; *toppling* $v$ removes $6$ chips from $v$ and adds one chip to each of its six neighbors. A *toppling sequence* is a finite or infinite sequence of vertices, toppled in order from the starting configuration $S_0$; it is *legal* if every vertex toppled has at least 6 chips at that moment, and *complete* if every vertex that is unstable at some step, the start included, is toppled at that step or a later one. The *sandpile process* topples the vertices of a legal complete sequence; such sequences exist, and by the *abelian property* the number of times $N(v) \in \mathbb{N} \cup \{\infty\}$ that a vertex $v$ topples (the *odometer*) is the same for all of them. The process *halts* if some legal complete sequence is finite.

A configuration $S$ is *periodic* if there are integers $n_x, n_y, n_z \ge 1$ such that $S(x, y, z) = S(x', y', z')$ whenever $x \equiv x' \bmod n_x$, $y \equiv y' \bmod n_y$ and $z \equiv z' \bmod n_z$; it is given finitely by the three periods and its values on the box $[0, n_x) \times [0, n_y) \times [0, n_z)$. A *periodic-plus-finite* (p+f) sandpile is a periodic configuration with finitely many chips added at finitely many vertices, given by the periodic data and the finite list of additions. The three decision problems on a given p+f sandpile are:

- *vertex prediction*: does the origin topple at least once, that is, is $N(0) \ge 1$?
- *global halting prediction*: are there infinitely many topplings in total, that is, is $\sum_{v} N(v) = \infty$?
- *local halting prediction*: does the origin topple infinitely often, that is, is $N(0) = \infty$?

For a periodic configuration alone, the odometer equals that of the same configuration on the finite torus $\mathbb{Z}/n_x \times \mathbb{Z}/n_y \times \mathbb{Z}/n_z$, so all three questions are decidable, and a configuration with finitely many chips on $\mathbb{Z}^3$ always halts; it is the combination that makes them hard.

## Depends on

None.

## Proof depends on

None.

## Sources

- H. Cairns, "Some Halting Problems for Abelian Sandpiles Are Undecidable in Dimension Three", *SIAM Journal on Discrete Mathematics* 32(4):2636–2666, 2018, doi:[10.1137/16M1091964](https://doi.org/10.1137/16M1091964); numbering of arXiv:1508.00161v2: Section 1 (the sandpile process, legal and complete toppling sequences and the abelian property, Lemmas 1–3), the subsections on periodic and on periodic+finite sandpiles in Section 1 with the definitions of the three problems, and the appendix (torus lemma and halting of finite sandpiles).
