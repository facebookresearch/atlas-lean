# Strict separation of arithmetic formulas from affine branching programs

Fix any field $F$. At each natural index $n$ a family consists of a formal multivariate polynomial $p_n$ over $F$ with its own finite variable type. The cardinality of that type and the total degree of $p_n$ are each bounded by $A n^d$ for some natural $A,d$ and all sufficiently large $n$. Let $\mathsf{VF}$ consist of such families computed exactly by formula trees of polynomially bounded size, counting one per binary addition, subtraction or multiplication and zero for field constants and variables. Let $\mathsf{VBP}$ use affine branching programs of polynomially bounded size: a finite DAG in topological order with first vertex of value $1$, subsequent vertices valued by the sum of predecessor values times their incoming affine-linear labels, and a chosen output vertex. A row without incoming edges has value zero, parallel edges are counted separately, and size counts vertices plus edges. Both models compute identities in the formal polynomial ring, not just evaluations on $F$-points.

Over every field $F$, $\mathsf{VF}(F)$ is a strict subset of $\mathsf{VBP}(F)$ on this common set of families.

## Depends on

- The exact arithmetic formula tree and the topologically ordered affine branching program above.

## Proof depends on

- Exact formulas-to-ABP compilation with polynomial overhead and an explicit family accessible by polynomial-size branching programs but admitting no polynomial-size formula family.

## Expansion

Give formal-polynomial evaluators and their size bounds, identify the dependency on the separation family, and state its lower bound without assuming degree or field-characteristic restrictions absent here. A definition of weakly skew circuits by itself is not a bridge to this ABP encoding.

## Sources

- OpenAI, [family bounds, formulas, affine programs and first strict inclusion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ArithmeticHierarchy.lean#L47-L212).
