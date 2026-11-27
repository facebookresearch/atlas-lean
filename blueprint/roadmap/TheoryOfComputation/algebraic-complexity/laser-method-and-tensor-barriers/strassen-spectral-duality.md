# Strassen's spectral characterization of asymptotic rank and subrank

For every tensor $T$ over a field,

$$
\underset{\sim}{R}(T) = \max_{F \in \Delta} F(T), \qquad \underset{\sim}{Q}(T) = \min_{F \in \Delta} F(T),
$$

and $\omega = \log_2 \underset{\sim}{R}(\langle 2, 2, 2 \rangle)$. Over $\mathbb{C}$, the **quantum functionals** $F^{\theta}(T) = 2^{\max_{\mu} \sum_i \theta_i H(\mu_i)}$, where $\mu$ ranges over the entanglement polytope of $T$ and $\theta$ over probability vectors on the three factors, are points of $\Delta$ for every $\theta$.

## Proof sketch

The duality is an instance of Strassen's Positivstellensatz for preordered commutative semirings satisfying a boundedness (Archimedean) condition: the semiring of tensors with restriction preorder satisfies it, and the asymptotic preorder is characterized by monotone homomorphisms to the nonnegative reals. The quantum functionals are monotone and multiplicative by properties of moment polytopes under tensor products and restrictions.

## Depends on

- [Strassen's asymptotic spectrum of tensors and asymptotic rank](asymptotic-spectrum.md)
- [Matrix multiplication exponent](../matrix-multiplication-exponent/matrix-multiplication-exponent.md)

## Sources

- V. Strassen, "The asymptotic spectrum of tensors", Journal für die reine und angewandte Mathematik 384 (1988) 102-152.
- M. Christandl, P. Vrana, J. Zuiddam, "Universal points in the asymptotic spectrum of tensors", Journal of the American Mathematical Society 36 (2023); STOC (2018), arXiv:1709.07851.
