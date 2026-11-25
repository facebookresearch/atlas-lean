# Radical of an ideal

The radical of an ideal $I$ of a commutative ring $R$ is the set $\sqrt{I}$ of the elements $f \in R$ with $f^n \in I$ for some integer $n \ge 1$. Mathlib defines it more generally, for ideals of commutative semirings. Let $R$ be a commutative semiring and $I$ an ideal of $R$. The radical of $I$ is the ideal of $R$ consisting of the $r \in R$ with $r^n \in I$ for some natural number $n$, where $n = 0$ is allowed. Allowing $n = 0$ adds no elements: $r^0 = 1 \in I$ forces $I = R$, and then already $r^1 = r \in I$. The radical is defined for every ideal, including $I = R$, whose radical is $R$. It is not to be confused with the property of an ideal of being radical, which says that the ideal contains its radical, nor with the Jacobson radical of $R$. For a commutative ring with identity this gives the familiar definition.

## Sources

- David Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate Texts in Mathematics 150, Springer-Verlag, 1995.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the commutative semiring hypothesis: `CommSemiring`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Ideal/Operations.lean#L549.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the different property of an ideal being radical: `Ideal.IsRadical`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Ideal/Operations.lean#L803-L805.
