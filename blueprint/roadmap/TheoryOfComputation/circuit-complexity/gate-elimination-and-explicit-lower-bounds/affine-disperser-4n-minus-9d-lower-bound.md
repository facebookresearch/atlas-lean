# A 4n - 9d lower bound for affine dispersers

Every circuit over the full binary basis computing an affine disperser for dimension $d$ on $n$ bits has at least $4n-9d$ genuinely binary gates. Consequently there is a language in $\mathsf{P}$ whose slices on $N$ bits require $B_2$-circuits with at least $4N-O(N^{4/5})$ binary gates for all sufficiently large $N$.

## Proof sketch

A refinement of gate elimination that tracks pairs of variables constrained to the zero locus of a quadratic relation, with an amortized potential accounting showing an average saving of four gates per step. Applying it to an explicit affine disperser for dimension $d=O(N^{4/5})$ computable in polynomial time gives the explicit corollary.

## Depends on

- [Affine dispersers](affine-dispersers.md)
- [The full binary basis B2 and the basis U2](../circuit-models-and-complexity-measures/full-binary-basis-b2-and-u2.md)

## Proof depends on

- [Fair semi-circuits over the full binary basis](fair-semi-circuits.md)
- [A 3.5n - 7d lower bound for affine dispersers](affine-disperser-3-5n-minus-7d-lower-bound.md)

## Sources

- Om Swostik Mishra, Rahul Santhanam, "An Explicit 4n - O(\log n) Size Lower Bound against General Boolean Circuits", 2027.
- Om Swostik Mishra, Rahul Santhanam, "An Explicit 4n - O(\log n) Size Lower Bound against General Boolean Circuits", Electronic Colloquium on Computational Complexity, 2026.
- Xin Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th Annual IEEE Symposium on Foundations of Computer Science, 2023.
