# Independent set games with entangled players are RE-complete

There are a constant $s < 1$ and a number $t$ of questions such that deciding whether a succinctly presented $t$-independent set game has quantum value 1 or less than $s$ is RE-complete, although its classical counterpart is decidable in polynomial time.

**Independent set games.** For a finite simple graph $X$ with vertex set $\mathcal V(X)$ and a positive integer $t$, the *$t$-independent set game* for $X$ has question set $[t]$ for both players, answer set $\mathcal V(X)$, and predicate $V(i, j; u, v) = 1$ iff $u = v$ when $i = j$, and $u, v$ are distinct non-adjacent vertices when $i \neq j$. Its question distribution is either uniform on $[t] \times [t]$ or the diagonally weighted distribution $\pi_d(i, j) = \frac{1}{2t}\delta_{i,j} + \frac{1}{2t^2}$. The players try to convince the referee that $X$ has an independent set of size $t$. For a family $C$ of games and $0 < s \leq 1$, the *$(1, s)$-gap$^*$ problem* for $C$ asks, given a game $\mathcal G \in C$, whether its [entangled (quantum) value](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/entangled-strategies-and-entangled-value.md) satisfies $\omega^*(\mathcal G) = 1$ or $\omega^*(\mathcal G) < s$, under the promise that one holds. A family of games is *succinctly presented* if Turing machines running in time polynomial in the family parameter sample the questions and evaluate the predicate.

**Theorem (Mančinska, Spaas, Spirig and Vernooij).** There exist a constant $0 < s < 1$, a positive integer $t$, and a succinctly presented family $C$ of $t$-independent set games such that the $(1, s)$-gap$^*$ problem for $C$ is RE-complete (Corollary B of arXiv:2505.05253v2).

According to the source, an exponential-time reduction then shows that for this $s$ the $(1, s)$-gap$^*$ problem is undecidable for explicitly given $t$-independent set games, whereas for each fixed $t$ the classical question whether $X$ has an independent set of size $t$ is decidable in polynomial time.

## Depends on

- [Finite simple graph](../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Entangled strategies and the entangled value of a game](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/entangled-strategies-and-entangled-value.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem reduces to the entangled value gap problem](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/halting-problem-reduces-to-entangled-value-gap.md)
- [MIP* is contained in RE](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/mip-star-is-contained-in-re.md)

## Expansion

The main step (Theorem A of the source) is a gap-preserving reduction: for a synchronous game $\mathcal G$ with uniform question distribution and $t$ questions, take the $t$-independent set game of its game graph $X(\mathcal G)$, whose vertices are question–answer pairs $(q, a)$, adjacent when the predicate rejects the pair of answers. If $\omega^*(\mathcal G) = 1$ then the new game has value 1, and if $\omega^*(\mathcal G) < 1 - \varepsilon$ then its value is less than $1 - O(\varepsilon^8 / t^4)$. The soundness rests on a new stability theorem for approximate projection-valued measurements in tracial von Neumann algebras. Applied to the RE-complete family of synchronous games with constant question size and uniform question distribution of Natarajan and Zhang, this gives the corollary; membership in RE follows from $\mathrm{MIP}^* \subseteq \mathrm{RE}$. A good expansion links the theorem of Natarajan and Zhang and the stability theorem.

## Sources

- L. Mančinska, P. Spaas, T. Spirig and M. Vernooij, "Gap-preserving reductions and RE-completeness of independent set games", in *2025 IEEE 66th Annual Symposium on Foundations of Computer Science (FOCS 2025)*, IEEE, 2025, pp. 1074–1090, doi:10.1109/FOCS63196.2025.00056; read as arXiv:2505.05253v2, <https://arxiv.org/abs/2505.05253v2>: Section 1 (Theorem A, Corollary B and the discussion after them), the preliminaries on nonlocal games and complexity theory (the definitions of independent set games, of the game graph, of the gapped promise problem and of succinctly presented families) and the section on the approximate regime (the proof of Corollary B).
