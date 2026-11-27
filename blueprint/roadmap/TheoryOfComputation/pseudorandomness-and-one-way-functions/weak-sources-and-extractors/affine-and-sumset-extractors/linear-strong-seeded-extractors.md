# F2-linear strong seeded extractors

A strong $(k, \varepsilon)$-extractor $\mathrm{Ext} : \{0,1\}^n \times \Sigma \to \{0,1\}^m$ is *$\mathbb{F}_2$-linear* if $x \mapsto \mathrm{Ext}(x, s)$ is $\mathbb{F}_2$-linear for every seed $s$. Linearity lets such an extractor be applied to a sumset $A + B$: $\mathrm{Ext}(A + B, S) = \mathrm{Ext}(A, S) + \mathrm{Ext}(B, S)$, so its output stays close to uniform jointly with $S$ and the entire second source $B$. Multiplication by a uniform $m \times n$ Boolean matrix is an example.

## Depends on

- [Seeded randomness extractors](../seeded-randomness-extractors.md)
- [Affine sources, affine extractors and sumset extractors](affine-sources-and-sumset-extractors.md)

## Sources

- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
