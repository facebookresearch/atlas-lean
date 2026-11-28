# Quillen equivalences

Let $C$ and $D$ be model categories and let $L : C \to D$ be left adjoint to $R : D \to C$. For objects $X$ of $C$ and $Y$ of $D$, write $\tilde f : X \to R(Y)$ for the morphism that corresponds to $f : L(X) \to Y$ under the adjunction. The adjunction $L \dashv R$ is a Quillen equivalence when it is a [Quillen adjunction](../quillen-adjunctions-and-quillen-functors/is-quillen-adjunction.md) and, for every cofibrant object $X$ of $C$, every fibrant object $Y$ of $D$ and every morphism $f : L(X) \to Y$, $f$ is a weak equivalence of $D$ if and only if $\tilde f$ is a weak equivalence of $C$.

## Sources

- M. Hovey, *Model categories*, Mathematical Surveys and Monographs 63, American Mathematical Society, 1999, Definition 1.3.12.
