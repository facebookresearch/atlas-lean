# Only countably many bit-string functions are computable

The set of total functions $\{0,1\}^*\to\{0,1\}^*$ computable by deterministic multi-tape Turing machines is countable, while the set of all such functions has the cardinality of the continuum $2^{\aleph_0}$. Hence most functions (and most languages, and most languages in no complexity class) are not computable; likewise there are only countably many languages in $\mathsf{P}$.

## Proof sketch

Each machine has a finite description, so computable functions are the image of a countable set; Cantor's diagonal argument shows that $\{0,1\}^{\{0,1\}^*}$, and hence the function space, is uncountable.

## Depends on

- [Polynomial-time computable functions](../../the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 0–2", 2006, Theorem 1.4.
