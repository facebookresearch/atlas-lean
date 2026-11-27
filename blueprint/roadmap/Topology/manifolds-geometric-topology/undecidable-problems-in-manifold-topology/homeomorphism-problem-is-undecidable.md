# The homeomorphism problem for closed manifolds of dimension at least four is undecidable

For every $n \ge 4$ there is no algorithm that decides, given two triangulated connected closed orientable $n$-manifolds, whether they are homeomorphic. This is Markov's theorem of 1958; it rests on the undecidability of the triviality problem for finitely presented groups.

Fix $n \ge 4$. The inputs are pairs $(K_1, K_2)$ of finite simplicial complexes whose realizations $|K_1|, |K_2|$ are connected closed orientable PL $n$-manifolds.

**Theorem (Markov).** For every $n \ge 4$ there is no algorithm that takes as input two connected closed orientable $n$-dimensional PL manifolds $K_1, K_2$, given by triangulations, and decides whether $|K_1|$ is homeomorphic to $|K_2|$.

Conventions: the theorem is about a fixed dimension, with both manifolds part of the input. The exposition read below states, as a consequence of geometrization, that the problem is solved for closed orientable manifolds of dimension at most $3$, and it gives detailed proofs that the same construction yields undecidability for PL homeomorphism, homotopy equivalence, and isomorphism of fundamental groups as well.

## Depends on

- [Algorithmic recognition problem for a manifold](recognition-problem-for-a-manifold.md)
- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Closed manifold, not required to be connected](../closed-topological-manifold.md)
- [R-orientation of a topological manifold](../../algebraic-topology/homological-orientation.md)
- [Homeomorphism](../../topological-spaces/homeomorphism.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

There is no algorithm deciding whether a finite group presentation presents the trivial group (Theorem 3.1 of the note, attributed to Novikov; it is also a consequence of the Adian–Rabin theorem). From a presentation $P = \langle g_1, \dots, g_k \mid r_1, \dots, r_l \rangle$ one effectively builds a PL $(n+1)$-manifold $W$ that PL-embeds into $\mathbb{R}^{n+1}$ and has a handle decomposition realizing $P$ (Definition 2.2 of the note): attach $k$ one-handles to the $(n+1)$-ball, then $l$ two-handles along curves representing the relators, and finally $k$ further two-handles. The inclusion $\partial W \to W$ induces an isomorphism of fundamental groups, so $\pi_1(\partial W)$ is the group presented by $P$. Markov's lemma (Lemma 2.6 of the note) says that $P$ presents the trivial group if and only if $\partial W$ is PL-homeomorphic to the connected sum $\#_l (S^2 \times S^{n-2})$ of $l$ copies of $S^2 \times S^{n-2}$: when the group is trivial, the last $k$ two-handles cancel the one-handles, and the embedding into $\mathbb{R}^{n+1}$ forces the remaining $l$ two-handles to be attached in an untwisted way. An algorithm deciding homeomorphism, applied to $\partial W$ and a triangulation of $\#_l (S^2 \times S^{n-2})$, would therefore decide triviality. Gordon's theorem (Theorem 4.1 of the note) gives, for every $l \ge 13$, a set of presentations with exactly $l$ relations on which triviality is undecidable, which makes $\#_l (S^2 \times S^{n-2})$ a fixed unrecognizable manifold (Theorem 1.5 of the note). A good expansion links the triviality theorem, Markov's lemma and the algorithmic construction of $W$, which have no pages here.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where Section 7.1 ("The homeomorphism problem") states that for each $d \ge 4$ the homeomorphism problem for $d$-manifolds is undecidable, as proved by Markov.
- Alexander V. Chernavsky and Vladimir P. Leksine, *Unrecognizability of manifolds*, Ann. Pure Appl. Logic 141 (2006), no. 3, 325–335, https://doi.org/10.1016/j.apal.2005.12.011, a refereed account of Markov's theorem and its proof, cited beside the copies read here.
- Stefan Friedl, Tobias Hirsch and Marc Kegel, *The unsolvability of the homeomorphism problem*, expository note, read in the copy arXiv:2603.23630v1, whose numbering is used here: Theorem 1.1 states the result for PL homeomorphism and Theorem 1.2 covers homeomorphism and further equivalence relations, with Definition 2.2 and Lemma 2.6 in Section 2, the proof in Section 3 and Gordon's strengthening as Theorem 4.1 in Section 4; it attributes the theorem to Markov's 1958 work.
- A. A. Markov, *The insolubility of the problem of homeomorphy* (in Russian), Dokl. Akad. Nauk SSSR 121 (1958), 218–220, the original announcement, cited beside the copies read above.
