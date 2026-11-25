# Character of a representation

The character of a finite-dimensional complex representation $\rho$ of a finite group $G$ is the function $G \to \mathbb{C}$ sending $g$ to the trace of the linear map $\rho(g)$. Mathlib defines the character for representations of any monoid over any field. Let $k$ be a field, $G$ a monoid, $V$ a vector space over $k$, and $\rho$ a representation of $G$ on $V$, that is, a monoid homomorphism $g \mapsto \rho(g)$ from $G$ to the $k$-linear endomorphisms of $V$. The character of $\rho$ is the function $\chi_\rho \colon G \to k$ with $\chi_\rho(g) = \operatorname{tr} \rho(g)$, where $\operatorname{tr}$ is Mathlib's trace: the trace of the matrix in a finite basis when $V$ is finite-dimensional, and $0$ otherwise. The character is attached to a given representation; the definition says nothing about which functions arise as characters. For a finite group acting on a finite-dimensional complex vector space, each $\rho(g)$ is invertible and this gives the familiar character.

## Sources

- Jean-Pierre Serre, Linear Representations of Finite Groups, Graduate Texts in Mathematics 42, Springer-Verlag, 1977.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for representations as monoid homomorphisms to linear endomorphisms: `Representation`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RepresentationTheory/Basic.lean#L46-L49.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the trace of an endomorphism, $0$ when there is no finite basis: `LinearMap.trace`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Trace.lean#L72-L76.
