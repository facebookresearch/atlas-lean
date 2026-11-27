# Krull dimension of a commutative semiring

Let $R$ be a commutative semiring with identity, for example a commutative ring with identity. A *chain of prime ideals of length $n$* in $R$, where $n \ge 0$ is an integer, is a sequence $P_0 \subsetneq P_1 \subsetneq \cdots \subsetneq P_n$ of prime ideals of $R$. The *Krull dimension* $\dim R$ of $R$ is the supremum of the lengths of all chains of prime ideals in $R$, taken in $\{-\infty\} \cup \{0, 1, 2, \dots\} \cup \{\infty\}$. So $\dim R = \infty$ when there are chains of every finite length, and $\dim R = -\infty$ when $R$ has no prime ideal, as for the zero ring. A nonzero commutative ring with identity has a maximal ideal, which is prime, so its Krull dimension is at least $0$.

## Sources

- David Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate Texts in Mathematics 150, Springer-Verlag, 1995.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the Krull dimension of a commutative semiring as the Krull dimension of its set of prime ideals ordered by inclusion: `ringKrullDim`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/KrullDimension/Basic.lean#L26-L30.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the Krull dimension of a preordered set as the supremum of the lengths of its strictly increasing finite chains, with values in the natural numbers extended by −∞ and +∞, and equal to −∞ for the empty set: `Order.krullDim`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Order/KrullDimension.lean#L73-L80.
