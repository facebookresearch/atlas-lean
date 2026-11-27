# The homeomorphism problem for closed manifolds of dimension at least four is undecidable

For every $n \ge 4$ there is no algorithm that decides, given two triangulated connected closed orientable $n$-manifolds, whether they are homeomorphic. This is Markov's theorem of 1958; it rests on the undecidability of the triviality problem for finitely presented groups.

Fix $n \ge 4$. The inputs are pairs $(K_1, K_2)$ of finite simplicial complexes whose realizations $|K_1|, |K_2|$ are connected closed orientable PL $n$-manifolds.

**Theorem (Markov).** For every $n \ge 4$ there is no algorithm that takes as input two connected closed orientable $n$-dimensional PL manifolds $K_1, K_2$, given by triangulations, and decides whether $|K_1|$ is homeomorphic to $|K_2|$.

Conventions: the theorem is about a fixed dimension, with both manifolds part of the input. The exposition read below states, as a consequence of geometrization, that the problem is solved for closed orientable manifolds of dimension at most $3$, and it gives detailed proofs that the same construction yields undecidability for PL homeomorphism, homotopy equivalence, and isomorphism of fundamental groups as well.

## Depends on

- [Algorithmic recognition problem for a manifold](recognition-problem-for-a-manifold.md)

## Proof depends on

None.

## Expansion

There is no algorithm deciding whether a finite group presentation presents the trivial group (a theorem the note attributes to Novikov, also a consequence of the Adian–Rabin theorem); moreover there is a finite list of relators, with fixed numbers of generators and relators, for which the problem is already undecidable. From a presentation $P$ with $g$ generators and $r$ relators one builds a closed orientable $n$-manifold $M_P$: take the boundary of a regular neighborhood of an embedding of the presentation $2$-complex into $\mathbb{R}^{n+1}$, or attach $g$ one-handles and $r$ two-handles to the $(n+1)$-ball along curves read off the relators and take the boundary. Then $\pi_1(M_P)$ is the group presented by $P$, and when the group is trivial, $M_P$ is homeomorphic to the connected sum of $r$ copies of $S^2 \times S^{n-2}$, because the embedding into $\mathbb{R}^{n+1}$ forces the two-handles to be attached in an untwisted way. Hence an algorithm deciding homeomorphism to $\#_r (S^2 \times S^{n-2})$ would decide triviality of the groups in the list.

## Sources

- Alexander V. Chernavsky and Vladimir P. Leksine, *Unrecognizability of manifolds*, Ann. Pure Appl. Logic 141 (2006), no. 3, 325–335, https://doi.org/10.1016/j.apal.2005.12.011, a refereed account of Markov's theorem and its proof, cited beside the copy read below.
- Stefan Friedl, Tobias Hirsch and Marc Kegel, *The unsolvability of the homeomorphism problem*, expository note, read in the copy arXiv:2603.23630v1, whose numbering is used here: Theorem 1.1 states the result for PL homeomorphism and Theorem 1.2 covers homeomorphism and further equivalence relations, with the proof in Section 3; it attributes the theorem to Markov's 1958 work.
- A. A. Markov, *The insolubility of the problem of homeomorphy* (in Russian), Dokl. Akad. Nauk SSSR 121 (1958), 218–220, the original announcement, cited beside the copy read above.
