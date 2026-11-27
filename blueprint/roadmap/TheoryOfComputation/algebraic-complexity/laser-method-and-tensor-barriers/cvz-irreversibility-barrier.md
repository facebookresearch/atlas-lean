# Christandl–Vrana–Zuiddam irreversibility barrier for the laser method

For a tensor $T$ define its **irreversibility** $i(T) = \log \underset{\sim}{R}(T) / \log \underset{\sim}{Q}(T) \ge 1$. Any approach that obtains bounds on $\omega$ by degenerating powers of an intermediate tensor $T$ to matrix multiplication tensors (including the laser method and its asymmetric variants) is limited by the irreversibility of $T$: every upper bound on $\omega$ obtained by degenerating powers of $T$ into powers of matrix multiplication tensors is at least $2\, i(T)$. For the Coppersmith-Winograd tensors $\mathrm{CW}_q$ (see [The Coppersmith–Winograd tensor](cw-tensor.md)), lower bounds on $i(\mathrm{CW}_q)$ from Strassen's support functionals (which for these free tensors agree with the quantum functionals) show that every upper bound on $\omega$ obtained by degenerating powers of $\mathrm{CW}_q$ is at least $2.16805$ for every $q \ge 1$; this barrier is attained at $q = 1$, equals $2.17795$ at $q = 2$, increases with $q$ and tends to $3$.

## Proof sketch

Matrix multiplication tensors have irreversibility $\omega/2$, and irreversibility is submultiplicative under degeneration chains: if $\langle n,n,n\rangle^{\otimes a}$ is obtained from $T^{\otimes b}$, comparing asymptotic rank and subrank through monotone spectral points yields $\omega/2 \ge$ a quantity controlled by $i(T)$. Upper bounds on the asymptotic subrank of $\mathrm{CW}_q$ come from the minimum over quantum functionals, computed via entropy maximization over its moment polytope.

## Depends on

- [The Coppersmith–Winograd tensor](cw-tensor.md)
- [Strassen's asymptotic spectrum of tensors and asymptotic rank](asymptotic-spectrum.md)
- [Matrix multiplication exponent](../matrix-multiplication-exponent/matrix-multiplication-exponent.md)

## Proof depends on

- [Strassen's spectral characterization of asymptotic rank and subrank](strassen-spectral-duality.md)

## Sources

- M. Christandl, P. Vrana, J. Zuiddam, "Barriers for fast matrix multiplication from irreversibility", Theory of Computing 17 (2021); CCC (2019), arXiv:1812.06952.
- J. Alman, V. Vassilevska Williams, "Limits on all known (and some unknown) approaches to matrix multiplication", FOCS (2018), arXiv:1810.08671.
