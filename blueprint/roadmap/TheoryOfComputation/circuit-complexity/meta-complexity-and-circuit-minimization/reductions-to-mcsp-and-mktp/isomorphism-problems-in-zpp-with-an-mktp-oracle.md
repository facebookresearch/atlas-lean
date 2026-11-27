# Isomorphism problems are in ZPP relative to MKTP

Graph Isomorphism, Linear Code Equivalence, Permutation Group Conjugacy and Matrix Subspace Conjugacy are all in $\mathrm{ZPP}^{\mathrm{MKTP}}$: an MKTP oracle decides them with zero-sided error, removing the error of earlier reductions to MCSP and MKTP.

An *isomorphism problem* has instances $x=(x_0,x_1)$ that determine a universe $\Omega_x$, a group $H_x$ acting on it, and two elements $\omega_0,\omega_1\in\Omega_x$; the question is whether some $h\in H_x$ has $h(\omega_0)=\omega_1$.

**Theorem (Allender–Grochow–van Melkebeek–Moore–Morgan).** $\mathrm{GI}\in\mathrm{ZPP}^{\mathrm{MKTP}}$. More generally, an isomorphism problem is in $\mathrm{RP}^{\mathrm{MKTP}}$ when (1) the uniform distribution on $H_x$ is samplable in polynomial time and the action is computable in ZPP, and (2) some complete invariant of the representation of $\Omega_x$ is computable in ZPP; it is in $\mathrm{coRP}^{\mathrm{MKTP}}$ if in addition (3) there is a probably-approximately-correct overestimator for $\log(|H_x|/|\mathrm{Aut}(\omega)|)$ with deviation $1/4$ computable in randomized polynomial time with an MKTP oracle. The theorem gives sufficient group-theoretic conditions for (3), and these hold for:

- Linear Code Equivalence $\in\mathrm{ZPP}^{\mathrm{MKTP}}$,
- Permutation Group Conjugacy $\in\mathrm{ZPP}^{\mathrm{MKTP}}$,
- Matrix Subspace Conjugacy $\in\mathrm{ZPP}^{\mathrm{MKTP}}$.

## Expansion

The no-false-negative direction is new: pick random bits $r_1,\dots,r_t$ and random group elements $\pi_i$ and form $y=\pi_1(\omega_{r_1})\cdots\pi_t(\omega_{r_t})$. If $\omega_0$ and $\omega_1$ are not isomorphic, $y$ carries about $t(s+1)$ bits of entropy with $s=\log(|H_x|/|\mathrm{Aut}|)$, so $\mathrm{KT}(y)$ exceeds a threshold $\theta$ with high probability. If they are isomorphic, $y$ is determined by $t$ group elements, and an efficiently decodable near-optimal encoding (Lehmer codes and blocking) shows $\mathrm{KT}(y)\le\theta$ always. The inversion argument supplies the other one-sided algorithm, and the two together give zero error.

## Depends on

- [KT complexity and the minimum KT problem MKTP](kt-complexity-and-mktp.md)
- [Isomorphism of graph codes](../../../fine-grained-complexity/graph-isomorphism-in-quasipolynomial-time/isomorphic.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)
- [The class RP](../../../complexity-classes/time-and-space-complexity-classes/rp.md)

## Proof depends on

- [Dense KT-random oracles invert polynomial-time functions](kt-random-oracles-invert-polynomial-time-functions.md)

## Sources

- Eric Allender, Joshua A. Grochow, Dieter van Melkebeek, Cristopher Moore, Andrew Morgan, "Minimum Circuit Size, Graph Isomorphism, and Related Problems", *SIAM Journal on Computing* 47(4), 2018, https://doi.org/10.1137/17m1157970, arXiv:1710.09806v1 (Definition 1, Theorems 1 to 3, Corollaries 2 to 4).
