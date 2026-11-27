# Only countably many bit-string functions are computable

The set of total functions $\{0,1\}^*\to\{0,1\}^*$ computable by deterministic multi-tape Turing machines is countable, while the set of all such functions has the cardinality of the continuum $2^{\aleph_0}$. Hence all but countably many functions, and all but countably many languages, are not computable; in particular only countably many languages lie in $\mathsf{P}$.

## Proof sketch

Each machine has a finite description, so computable functions are the image of a countable set; Cantor's diagonal argument shows that $\{0,1\}^{\{0,1\}^*}$, and hence the function space, is uncountable.

## Depends on

- [Polynomial-time computable functions](../../the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Theorem 1.4.
