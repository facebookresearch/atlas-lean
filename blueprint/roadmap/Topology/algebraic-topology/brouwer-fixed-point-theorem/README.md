# Brouwer fixed-point theorem

Every continuous map of a simplex (equivalently, of a closed ball, or of any nonempty compact convex subset of a finite-dimensional real normed space) to itself has a fixed point. The simplex case follows by the combinatorial route of Knaster, Kuratowski and Mazurkiewicz (1929): Sperner's lemma gives fully labelled cells in finer and finer subdivisions, compactness turns them into the [Knaster–Kuratowski–Mazurkiewicz lemma](../../../Geometry/convex-geometry/kkm-lemma.md), and applying that lemma to the sets $\{x : f(x)_i \leq x_i\}$ yields a fixed point. Products of simplices are retracts of a simplex (product distribution, then marginals), which gives the theorem for them too, in the form Nash used to prove that every finite game has a mixed equilibrium. The same path from Sperner to Brouwer is why finding approximate Brouwer fixed points lies in the complexity class PPAD.

- [The Brouwer sets satisfy the KKM covering condition](exists-pos-weights-le.md)
- [Brouwer's fixed-point theorem for the standard simplex](exists-fixed-point.md)
- [Brouwer's fixed-point theorem for simplices with any finite vertex set](exists-fixed-point-of-finite.md)
- [Probability vector from a function](of-fun.md)
- [Continuity criterion for maps into a simplex](continuous-of-continuous-weights.md)
- [Product distribution](prod-simplex.md)
- [Weights of a pushforward distribution](map-weights-apply.md)
- [The marginals of a product distribution are its factors](marginal-prod-simplex.md)
- [The product distribution depends continuously on its factors](continuous-prod-simplex.md)
- [Brouwer's fixed-point theorem for products of simplices](exists-fixed-point-pi.md)

## Related topics

- [Sperner's lemma](../../../Combinatorics/polytopes-simplicial-complexes/sperner-s-lemma/README.md): the combinatorial lemma behind the KKM lemma.
- [Nash's theorem](../../../GameTheory/noncooperative-games/nash-s-theorem/README.md): the main application, through the product form.
- [PPAD and the END-OF-THE-LINE problem](../../../TheoryOfComputation/completeness-other-classes/ppad-and-the-end-of-the-line-problem/README.md): the complexity of computing approximate fixed points.
- [Fixed-point theory](../../../Analysis/fixed-point-theory/README.md): fixed points of nonexpansive and affine maps (Browder–Göhde–Kirk, Markov–Kakutani), which need no topology of the simplex.
