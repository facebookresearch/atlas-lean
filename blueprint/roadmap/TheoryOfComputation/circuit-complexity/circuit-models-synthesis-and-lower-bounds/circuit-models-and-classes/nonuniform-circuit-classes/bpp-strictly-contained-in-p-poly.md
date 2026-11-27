# BPP is strictly contained in P/poly

$\mathsf{BPP}\subsetneq\mathsf{P}/\mathsf{poly}$ for languages over $\{0,1\}$: every language decided by a polynomial-time bounded-error probabilistic machine has polynomial-size circuits (Adleman), while $\mathsf{P}/\mathsf{poly}$ contains undecidable languages and every language in $\mathsf{BPP}$ is decidable.

## Proof sketch

Inclusion is Adleman's theorem. Every $\mathsf{BPP}$ language is in $\mathsf{PSPACE}\subseteq\mathsf{EXP}$, hence decidable, whereas $\mathsf{P}/\mathsf{poly}$ has undecidable members.

## Depends on

- [BPP](../../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [Polynomial time with polynomial advice](../../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)

## Proof depends on

- [Adleman's theorem: BPP is contained in P/poly](../../../../randomized-and-quantum-complexity/adleman.md)
- [P/poly is uncountable and contains undecidable languages](p-poly-contains-undecidable-languages.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 6–7", 2007.
- Leonard Adleman, "Two Theorems on Random Polynomial Time", 19th Annual Symposium on Foundations of Computer Science, 1978.
