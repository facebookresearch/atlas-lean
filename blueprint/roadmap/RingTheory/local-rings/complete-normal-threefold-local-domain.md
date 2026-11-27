# Ring-theoretic properties of the completed surface-cone candidate

There exists a commutative complex algebra $R$ which is a Noetherian integrally closed local domain, complete for the adic topology of its maximal ideal $\mathfrak m$, with Krull dimension three and with $\mathbb C\to R/\mathfrak m$ bijective. The source realizes the existential by its completed surface cone. The comparator does not specify that ring in its type and does not say that it lacks a small Cohen–Macaulay module.

## Depends on

- [Adic completeness for multivariate power series](adic-completion/is-adic-complete-maximal-ideal.md), [regular locality for the finite-variable power series ring](regular-local-rings/mv-power-series-fin.md), and [the local residue field](local-rings-and-residue-fields/residue-field-local-ring.md).

## Proof depends on

- [Krull dimension of a univariate power series ring](regular-local-rings/power-series-over-a-regular-local-ring/ring-krull-dim-power-series.md), iterated from the complex field. For normality use the regular-local normality theorem in dimension three, or prove integral closure directly for the three-variable formal series ring. [The existing dimension-at-most-one normality result](regular-local-rings/is-domain-and-is-integrally-closed-of-ri.md) does not cover dimension three.

## Expansion

The statement is existential, so a candidate independent of the particular cone is $\mathbb C[[X,Y,Z]]$. Identify it with the triple iterated series ring to use the dimension increments; identify its residue map with extraction of the constant coefficient, so constants give its inverse. Use the linked finite-variable adic result over the complex field and bridge the relevant maximal ideal under the series equivalence. The remaining normality step is in dimension three, not the proved dimension-one special case. No small Cohen–Macaulay obstruction is needed or follows from this alternate witness.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SurfaceConeCandidateSupport.lean#L7-L14) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SurfaceConeCandidateSupport.lean).
