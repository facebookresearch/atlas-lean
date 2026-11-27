# Concentration of circuit complexity under product distributions

Under any product distribution on truth tables, the circuit size of a random Boolean function is sharply concentrated: with probability at least $1-2^{-n}$ it lies within $\sqrt{N}\,n^2$ of its mean, where $N=2^n$.

**Theorem (Golovnev–Ilango–Impagliazzo–Kabanets–Kolokolova–Tal).** For every $n\ge1$ let $\mu$ be a product distribution over $\{0,1\}^N$, $N=2^n$, and let

$$s^{\mu}_n=\mathbb{E}_{f\sim\mu}[\mathrm{size}(f)],$$

the expected minimum circuit size of an $n$-variable function whose truth table is drawn from $\mu$. If $f$ is drawn from $\mu$, then with probability at least $1-2^{-n}$,

$$|\mathrm{size}(f)-s^{\mu}_n|\le\sqrt{N}\cdot n^2.$$

The bound is only informative when it is below the typical size $\Theta(2^n/n)$ of a random function, which holds for all large $n$.

## Expansion

If $f$ and $g$ differ on one input $a$, then $|\mathrm{size}(f)-\mathrm{size}(g)|\le O(n)$: from a circuit $C$ for $f$ build $D(z)=(b\wedge[z=a])\vee(C(z)\wedge[z\ne a])$ with $b=g(a)$, adding $O(n)$ gates. So circuit size is a function of $N$ independent bits with bounded differences $O(n)$, and McDiarmid's inequality with deviation $\sqrt{N}\,n^2$ gives failure probability $\exp(-\Omega(n^2))\le 2^{-n}$.

## Depends on

- [Circuit complexity of a Boolean function and truth tables](../../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Proof depends on

None.

## Sources

- Alexander Golovnev, Rahul Ilango, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, Avishay Tal, "AC^0[p] Lower Bounds Against MCSP via the Coin Problem", *International Colloquium on Automata, Languages, and Programming (ICALP)*, 2019, https://doi.org/10.4230/LIPIcs.ICALP.2019.66 (Theorem 3.1).
