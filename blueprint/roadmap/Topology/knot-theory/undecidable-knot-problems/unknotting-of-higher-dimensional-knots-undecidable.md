# Unknotting of n-dimensional knots is undecidable for n at least three

For every $n \ge 3$ there is no algorithm that decides whether a given $n$-dimensional knot in $\mathbb{R}^{n+2}$, given by finite data, is unknotted; consequently the equivalence problem for $n$-knots is undecidable. For classical knots both problems are decidable.

An $n$-*dimensional knot* is a smooth embedding of $S^n$ in $\mathbb{R}^{n+2}$ (or $S^{n+2}$), or, in the PL form of the theorem, a PL embedding of the boundary of the standard $(n+1)$-simplex in $\mathbb{R}^{n+2}$. Two knots are *equivalent* if an ambient isotopy carries one to the other, and a knot is *unknotted* if it is equivalent to the standard embedding of $S^n$ as the unit sphere in a hyperplane of $\mathbb{R}^{n+2}$.

**Theorem (Nabutovsky–Weinberger).** For every fixed $n \ge 3$ there is no algorithm that decides whether a given $n$-dimensional knot $f$ is unknotted, where $f$ is given either as a PL embedding of the boundary of the standard $(n+1)$-simplex in $\mathbb{R}^{n+2}$ or as a smooth embedding of $S^n$ in $\mathbb{R}^{n+2}$ given by an $(n+2)$-tuple of trigonometric polynomials with rational coefficients in the spherical angles (Theorem 1 of the paper). Since unknotting is a subproblem of equivalence, the equivalence problem for $n$-dimensional knots is undecidable for $n \ge 3$.

Conventions: the dimension $n$ is fixed and the knot is the input, in either format of the theorem; the inputs are promised to be embeddings. For classical knots the survey read gives the input format: a finite sequence of distinct points of $\mathbb{Q}^3$, joined cyclically by segments, such that adjacent segments meet only at their shared endpoint and nonadjacent segments are disjoint. For classical knots ($n = 1$), Haken gave an algorithm deciding unknotting and, with Hemion's completion, equivalence; the equivalence problem for $2$-dimensional knots is left open by Nabutovsky and Weinberger.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The proof reduces the halting problem to triviality of knots. Kervaire showed that a finitely presented group $G$ with an element $w$ is the group of an $n$-knot for every $n \ge 3$ when $H_1(G) = \mathbb{Z}$, $H_2(G) = 0$ and $G$ is the normal closure of $w$. If $K$ is finitely presented with $H_1(K) = H_2(K) = 0$ and has an element $h$ with $K / [h, K]$ trivial, then $G = K \times \mathbb{Z}$ and $w = (h, 1)$ satisfy these conditions. From a finite presentation of such a $K$ one builds, for $n \ge 4$, the manifold $\Sigma^{n+1} \times S^1$, with $\Sigma^{n+1}$ Kervaire's homology sphere with fundamental group $K$; for $n = 3$ one uses instead Markov's $4$-manifold $M^4$ with fundamental group $K$, takes $M^4 \times S^1$, and does surgery on embedded $2$-spheres realizing a basis of $H_2(M^4)$. Surgery along a curve representing $(h, 1)$ then gives $S^{n+2}$, and the axis of the attached handle is a knot with group $K \times \mathbb{Z}$; when $K$ is trivial the curve is isotopic to a meridian and the knot is trivial. A trial-and-error search writes this knot in either input format. Lemma 2 of the paper constructs from a Turing machine and its input such a group $K$ that is trivial exactly when the machine halts. Its proof combines a finitely presented group and word that is trivial exactly when the machine halts, from the proof of the unsolvability of the word problem, with the Adian–Rabin witness group and the universal central extension of that group. A good expansion links Kervaire's realization of knot groups, Kervaire's homology spheres and Markov's $4$-manifold for $n = 3$, the surgery construction of the knot and Lemma 2.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where the definitions, the statement and the classical and $2$-dimensional cases are in Section 7.3 ("Knot theory").
- Alexander Nabutovsky and Shmuel Weinberger, *Algorithmic unsolvability of the triviality problem for multidimensional knots*, Comment. Math. Helv. 71 (1996), no. 1, 426–434, https://doi.org/10.1007/BF02566428, read in the scan of the published article at http://math.uchicago.edu/~shmuel/NW-knots.pdf: Theorem 1 on p. 426 (the statement and the input formats), its proof on pp. 427–429 and Lemma 2 on p. 429, proved on pp. 429–431.
