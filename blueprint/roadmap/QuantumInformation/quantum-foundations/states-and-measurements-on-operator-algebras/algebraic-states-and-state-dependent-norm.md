# States on star-ordered algebras, state-dependent norm and approximation

Let $\mathcal{A}$ be a unital $*$-algebra over $\mathbb{C}$ with a partial order compatible with the star structure (a star-ordered algebra, e.g. a C*-algebra or $M_d(\mathbb{C})$). A *state* is a positive linear functional $\varphi:\mathcal{A}\to\mathbb{C}$ with $\varphi(1) = 1$; examples are vector states $M\mapsto\langle\psi, M\psi\rangle$ and $M\mapsto\operatorname{Tr}(\rho M)$ on matrices. A state defines the *state-dependent seminorm* $\|a\|_\varphi = \sqrt{\operatorname{Re}\varphi(a^*a)}$, the seminorm of the GNS pre-inner product $\langle a,b\rangle_\varphi = \varphi(a^*b)$, which satisfies Cauchy-Schwarz $|\varphi(a^*b)|\le\|a\|_\varphi\|b\|_\varphi$ and $\|ca\|_\varphi\le\|a\|_\varphi$ whenever $c^*c\le1$. Two elements are *$\delta$-close in $\varphi$*, written $a\approx_\delta b$, if $\|a-b\|_\varphi\le\delta$; errors add along chains. For families $(A^q_a)$, $(B^q_a)$ indexed by questions $q$ drawn from a distribution $\mu$ and outcomes $a$, *family closeness* means $\mathbb{E}_{q\sim\mu}\sum_a\|A^q_a - B^q_a\|_\varphi^2\le\delta^2$. A state can be pulled back along a monotone star-homomorphism $f$, with $\|a\|_{\varphi\circ f} = \|f(a)\|_\varphi$.

## Depends on

- [Existence of a unit cyclic vector in the GNS space](../../../Analysis/operator-algebras/gns-construction/exists-gns-cyclic-vector.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
- M. de la Salle, "Orthogonalization of positive operator valued measures", Comptes Rendus. Mathematique 360:549-560, 2022.
