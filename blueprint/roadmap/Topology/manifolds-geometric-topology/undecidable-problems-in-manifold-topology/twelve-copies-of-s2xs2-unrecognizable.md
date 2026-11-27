# The connected sum of twelve copies of S²×S² is algorithmically unrecognizable

There is no algorithm that decides, given a triangulation of a closed $4$-manifold, whether it is homeomorphic to the connected sum $\#_{12}(S^2 \times S^2)$ of twelve copies of $S^2 \times S^2$. This is Gordon's sharpening of Markov's theorem.

Let $\#_{12}(S^2 \times S^2)$ denote the connected sum of $12$ copies of $S^2 \times S^2$, a closed simply connected smooth $4$-manifold.

**Theorem (Gordon).** There is no algorithm that takes as input a triangulation of a closed $4$-manifold $X$ and decides whether $X$ is homeomorphic to $\#_{12}(S^2 \times S^2)$.

Conventions: the input is a finite simplicial complex whose realization is a closed $4$-manifold; the target manifold is fixed. Markov's original argument gives the existence of some $\ell$ with $\#_\ell(S^2 \times S^2)$ unrecognizable without an explicit value; the statement with $\ell = 12$ is Gordon's. Gordon states the result up to homeomorphism; according to Dunfield, Kegel, Li and Ren the proof works in the smooth and PL categories as well, so that $\#_{12}(S^2 \times S^2)$ is also smoothly unrecognizable.

## Depends on

- [Algorithmic recognition problem for a manifold](recognition-problem-for-a-manifold.md)

## Proof depends on

- [The homeomorphism problem for closed manifolds of dimension at least four is undecidable](homeomorphism-problem-is-undecidable.md)

## Expansion

Markov's construction attaches handles to the $5$-ball along curves read off a group presentation with $r$ relators, and the boundary is homeomorphic to $\#_r(S^2 \times S^2)$ exactly when the presented group is trivial. The number of copies is therefore the number of relators in a family of presentations for which triviality is undecidable. Gordon's contribution is a family of presentations with undecidable triviality problem whose structure brings the number of copies down to $12$.

## Sources

- Cameron McA. Gordon, *On the homeomorphism problem for 4-manifolds*, New Zealand J. Math. 52 (2022), 821–826, https://doi.org/10.53733/205, the source of the theorem, cited beside the copy read below.
- Nathan M. Dunfield, Marc Kegel, Shana Yunsheng Li and Qiuyu Ren, *Uncomputable trisection invariants of 4-manifolds*, preprint, read in the copy arXiv:2608.27811v2, where the theorem is quoted from Gordon, in the smooth form, at the start of its section of proofs, with the remark on categories after it.
