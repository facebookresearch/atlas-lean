# Ginsburg–Rose characterization of sequential functions

A partial function $\alpha : A^* \to B^*$ is [sequential](sequential-and-subsequential-functions.md) if and only if

1. $\alpha$ preserves prefixes: $\alpha(1) = 1$, and $\alpha(xy)$ defined implies $\alpha(xy) \in \alpha(x) B^*$;
2. there is an integer $M$ such that $ua \in \mathrm{dom}(\alpha)$ and $\alpha(ua) = \alpha(u) y$ imply $|y| \le M$, for all $u \in A^*$ and $a \in A$;
3. $\alpha^{-1}(L)$ is regular for every regular language $L \subseteq B^*$ (Ginsburg and Rose).

## Depends on

- [Sequential and subsequential functions](sequential-and-subsequential-functions.md)

## Proof depends on

- [Choffrut's characterization of subsequential functions](choffrut-s-characterization-of-subsequential-functions.md)

## Sources

- J. Berstel, *Transductions and Context-Free Languages*, Teubner, 1979; electronic edition of Chapters I–IV, 2007, <http://www-igm.univ-mlv.fr/~berstel/LivreTransductions/LivreTransductions.pdf>: Theorem IV.2.8 (Ginsburg and Rose, 1966), its proof from Theorem IV.2.7, and Proposition IV.2.6.
