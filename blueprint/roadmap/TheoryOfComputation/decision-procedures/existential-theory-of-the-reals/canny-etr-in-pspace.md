# Canny: the existential theory of the reals is in PSPACE

The existential theory of the reals is decidable in polynomial space: there is an algorithm that, given a quantifier-free integer polynomial formula $\Phi(x_1,\dots,x_n)$ of encoding length $L$, decides whether $\Phi$ has a real solution using space polynomial in $L$. Hence $\mathrm{NP} \subseteq \exists\mathbb{R} \subseteq \mathrm{PSPACE}$.

## Proof sketch

Canny's main lemma decides, in polynomial space, the signs of several polynomials at the common zeros of a zero-dimensional polynomial system, using resultants (the generalized characteristic polynomial, which handles degenerate systems) and parallel (NC) sign-determination algorithms over integers of exponential magnitude. A homogenizing perturbation reduces nonemptiness of the solution set of a formula to sign conditions at finitely many such zeros (points of a bounded perturbed semialgebraic set in the cube $[-1,1]^n$), and the main lemma decides those. (Canny's roadmap algorithm is used for motion planning, not for this theorem.)

## Depends on

- [The existential theory of the reals](existential-theory-of-the-reals.md)
- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Modular evaluation and size bounds for integer terms](modular-evaluation-of-integer-terms.md)

## Sources

- J. Canny, "Some Algebraic and Geometric Computations in PSPACE", Proceedings of the 20th ACM Symposium on Theory of Computing (STOC), 460–467, 1988, Section 2 (main lemma) and Theorem 3.3.
- S. Basu, R. Pollack and M.-F. Roy, Algorithms in Real Algebraic Geometry, 2nd ed., Springer, 2006.
