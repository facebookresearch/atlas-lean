# Base change of $K(X)/(f)$ along a factorization of $f$ over $K'$

Let $K$ and $K'$
be fields with $K'$ a $K$-algebra, let $f \in K[X]$, and let $(g_i)_{i \in \iota}$ be a family
of irreducible polynomials in $K'[X]$, indexed by a finite type $\iota$, that are pairwise
non-associated and whose product $\prod_i g_i$ is associated (equal up to a unit) to the image
of $f$ in $K'[X]$. Then there is an isomorphism of $K'$-algebras

$$(K[X]/(f)) \otimes_K K' \cong \prod_{i \in \iota} K'[X]/(g_i),$$

where the tensor product is a $K'$-algebra through its right factor. For $p \in K[X]$ with
class $[p]$ in $K[X]/(f)$ and for $c \in K'$, it sends $[p] \otimes c$ to the family of the
classes of $c\,p$ modulo the $g_i$, with $p$ read in $K'[X]$.

## Sources

- This is the algebraic decomposition in ATLAS N86, Corollary 4.39 of [MIT 18.785 *Number Theory I*](https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/). The corresponding upstream declaration is [`TensorSplitting.adjoinRoot_tensor_algEquiv_prod` in `v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean`, lines 146--160, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Chapter4/TensorSplitting.lean#L146-L160). There, `L` is presented as `K[X] / (f)`, the extension `K' / K` is arbitrary, and the distinct irreducible factors of `f` over `K'` are represented here by `g`, `hirr`, `hne`, and `hprod`. The source assumes that `f` is irreducible and separable in order to say that `L / K` is a finite separable field extension. Those assumptions are not needed for this CRT decomposition of the explicitly presented algebra `AdjoinRoot f`; accordingly, this theorem makes no stronger field or finite-etale claim about its factors.
