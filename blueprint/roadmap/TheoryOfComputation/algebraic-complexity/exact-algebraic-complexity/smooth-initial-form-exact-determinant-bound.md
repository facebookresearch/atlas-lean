# Exact determinant bounds from smooth initial forms

Let $g\in\mathbb C[X_0,\ldots,X_{d-1}]$, $a\in\mathbb C^d$, and $d,r\ge2$. The degree-$r$ part $G$ of $g(a+X)$ is nonzero, the lower homogeneous parts vanish, and the only common zero of $G$ and all its first partial derivatives is $0$. For every size-$n$ exact determinant of $g$, $(r-1)(d-1)/(4e)\le n$. A size-$n$ border determinant means $n>0$ and a sequence of determinants of $n\times n$ complex affine-linear pencils, convergent to the polynomial coefficient by coefficient (for every monomial). A size-$n$ exact determinant means $n>0$ and equality with one determinant of such a pencil.

## Depends on

- Translation at $a$, homogeneous components, partial derivatives, and affine pencils.

## Proof depends on

- [Border bound](../border-complexity-and-geometric-complexity-theory/smooth-initial-form-border-determinant-bound.md).

## Proof outline

Use the given exact affine pencil at every index. Each coefficient sequence is constant at the corresponding coefficient of $g$, so it converges to that coefficient. Apply the border bound at the same size, preserving all initial-form hypotheses.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SmoothInitialForm.lean#L35-L53) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SmoothInitialForm.lean).
