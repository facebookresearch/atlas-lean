# Christandl–Vrana–Zuiddam irreversibility barrier for the laser method

For a tensor $T$ define its **irreversibility** $i(T) = \log \underset{\sim}{R}(T) / \log \underset{\sim}{Q}(T) \ge 1$. Any approach that obtains bounds on $\omega$ by degenerating powers of an intermediate tensor $T$ to matrix multiplication tensors (including the laser method and its asymmetric variants) is limited by the irreversibility of $T$: every upper bound on $\omega$ obtained by degenerating powers of $T$ into powers of matrix multiplication tensors is at least $2\, i(T)$. For the small Coppersmith-Winograd tensors $\mathrm{CW}_q$, the quantum functionals give $i(\mathrm{CW}_q) > 1$, implying that methods going through $\mathrm{CW}_q$ cannot prove $\omega < 2.16$ (with the exact constant depending on $q$).

## Proof sketch

Matrix multiplication tensors have irreversibility $\omega/2$, and irreversibility is submultiplicative under degeneration chains: if $\langle n,n,n\rangle^{\otimes a}$ is obtained from $T^{\otimes b}$, comparing asymptotic rank and subrank through monotone spectral points yields $\omega/2 \ge$ a quantity controlled by $i(T)$. Upper bounds on the asymptotic subrank of $\mathrm{CW}_q$ come from the minimum over quantum functionals, computed via entropy maximization over its moment polytope.

## Depends on

- [Strassen's spectral characterization of asymptotic rank and subrank](strassen-spectral-duality.md)
- [The Coppersmith–Winograd tensor](cw-tensor.md)

## Proof depends on

- [Strassen's spectral characterization of asymptotic rank and subrank](strassen-spectral-duality.md)
- [The Coppersmith–Winograd tensor](cw-tensor.md)

## Sources

- M. Christandl, P. Vrana, J. Zuiddam, "Barriers for fast matrix multiplication from irreversibility", Theory of Computing 17 (2021); CCC (2019), arXiv:1812.06952.
- J. Alman, V. Vassilevska Williams, "Limits on all known (and some unknown) approaches to matrix multiplication", FOCS (2018), arXiv:1810.08671.
