# The Grassmann linearity agreement test

Let $\ell < n$ and let $F$ assign to every $\ell$-dimensional subspace $L \subseteq \mathbb{F}_2^n$ a linear function $F[L] : L \to \mathbb{F}_2$. The **Grassmann test** samples $L, L'$ uniformly at random with $\dim(L \cap L') = \ell - 1$ and accepts iff $F[L]|_{L \cap L'} = F[L']|_{L \cap L'}$. An assignment is **global** if there is a linear $g : \mathbb{F}_2^n \to \mathbb{F}_2$ with $F[L] = g|_L$ for all $L$. Since each linear function on $L \cap L'$ has exactly two extensions to each of $L$ and $L'$, the test is a $2$-to-$2$ game on the Grassmann graph, with a constraint between $L$ and $L'$ (equivalently, a $2$-to-$1$ game between the $\ell$-dimensional subspaces $L$ and the $(\ell-1)$-dimensional subspaces $L \cap L'$).

## Depends on

- [d-to-d games and 2-to-2 constraints](d-to-d-games.md)
- [Zoom-in and zoom-out subgraphs of the Grassmann graph](grassmann-zoom.md)

## Sources

- S. Khot, D. Minzer, M. Safra, "On independent sets, 2-to-2 games, and Grassmann graphs", STOC (2017), ECCC TR16-124.
- I. Dinur, S. Khot, G. Kindler, D. Minzer, M. Safra, "Towards a proof of the 2-to-1 games conjecture?", STOC (2018), ECCC TR16-198.
