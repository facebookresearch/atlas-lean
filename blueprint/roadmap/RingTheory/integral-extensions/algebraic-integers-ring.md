# The elements integral over a commutative ring form a subalgebra

Let $R$ and $A$ be commutative rings with identity, with $A$ an $R$-algebra. An element $a \in A$ is *integral* over $R$ if it is a root of a monic polynomial with coefficients in $R$, mapped into $A$. The elements of $A$ that are integral over $R$ form an $R$-subalgebra of $A$, the *integral closure* of $R$ in $A$: it contains $0$, $1$ and the image of $R$, and it is closed under addition and multiplication. For $R = \mathbb{Z}$ and $A = \mathbb{C}$, the integral elements are the algebraic integers, so the set $\mathbb{A}$ of algebraic integers is a subring of $\mathbb{C}$: $0, 1 \in \mathbb{A}$, and $\alpha + \beta$, $\alpha - \beta$ and $\alpha\beta$ lie in $\mathbb{A}$ whenever $\alpha, \beta \in \mathbb{A}$.

## Sources

- Daniel A. Marcus, Number Fields, 2nd ed., Universitext, Springer, 2018.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for integral elements: `IsIntegral`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean#L50-L54.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the integral closure as a subalgebra: `integralClosure`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean#L222-L228.
