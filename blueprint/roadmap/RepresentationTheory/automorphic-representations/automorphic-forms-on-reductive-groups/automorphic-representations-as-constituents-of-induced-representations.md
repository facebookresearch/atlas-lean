# Automorphic representations as constituents of induced representations

Let $k$ be a number field and $G$ a connected reductive group over $k$. For a parabolic subgroup $P$ of
$G$ over $k$ with Levi factor $M$ and a cuspidal automorphic representation $\sigma = \bigotimes'_v \sigma_v$ of
$M(\mathbb{A})$, let $\mathrm{Ind}\, \sigma = \bigotimes'_v \mathrm{Ind}\, \sigma_v$ be the parabolically induced
representation of $G(\mathbb{A})$; a constituent of a representation is an irreducible subquotient of it.

1. **Local constituents** (Langlands). For almost all $v$, $\mathrm{Ind}\, \sigma_v$ has exactly one
   constituent $\pi_v^\circ$ containing the trivial representation of $G(\mathcal{O}_v)$, and the constituents
   of $\mathrm{Ind}\, \sigma$ are exactly the representations $\bigotimes'_v \pi_v$ with $\pi_v$ a constituent of
   $\mathrm{Ind}\, \sigma_v$ and $\pi_v = \pi_v^\circ$ for almost all $v$.
2. **Characterization** (Langlands). A representation $\pi$ of $G(\mathbb{A})$ is an
   [automorphic representation](automorphic-forms-and-automorphic-representations.md) if and only if it is
   a constituent of $\mathrm{Ind}\, \sigma$ for some parabolic subgroup $P$ over $k$ and some cuspidal
   automorphic representation $\sigma$ of $M(\mathbb{A})$.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](automorphic-forms-and-automorphic-representations.md), for automorphic and cuspidal automorphic representations
- [Tensor product theorem for automorphic representations](tensor-product-theorem.md), for the restricted tensor products $\bigotimes'_v \sigma_v$ and $\bigotimes'_v \pi_v$
- [Parabolic induction and Jacquet functors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for the local induced representations $\mathrm{Ind}\, \sigma_v$ at the finite places

## Proof depends on

- [Finite length of parabolically induced representations](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/finite-length-of-induced-representations.md), for the finite composition series of $\mathrm{Ind}\, \sigma_v$ at the finite places, used in item 1
- [Harish-Chandra modules](../../reductive-groups-over-local-fields/representations-of-real-reductive-groups/harish-chandra-modules.md), for the finite length of the induced Harish-Chandra modules at the infinite places, which are finitely generated
- [Borel–Casselman theorem on Iwahori-fixed vectors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/borel-casselman-theorem.md), for the unramified principal series and the embedding of the irreducible representations with Iwahori-fixed vectors into them
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the decomposition $G(k_v) = P_0(k_v) G(\mathcal{O}_v)$ for a good maximal compact subgroup, by which the $G(\mathcal{O}_v)$-fixed vectors of an unramified principal series form a line (a fixed vector is determined by its value at $1$), which gives the unique unramified constituent $\pi_v^\circ$
- [Eisenstein series and their meromorphic continuation](eisenstein-series.md), for the "if" direction of item 2, where the constituents of $\mathrm{Ind}\, \sigma$ are realized in spaces of automorphic forms through the Taylor coefficients, at the given point, of Eisenstein series multiplied by a polynomial that clears their poles (Langlands's Proposition 2), not merely through residues; and, in the "only if" direction, for Langlands's vanishing lemma (an automorphic form whose constant terms are all orthogonal to cusp forms is zero; Langlands's Lemma 5)
- [Constant terms and Harish-Chandra's convolution identity for automorphic forms](constant-terms-and-convolution-identity.md), for the "only if" direction of item 2: the finiteness of automorphic forms under the centre (Langlands's Lemma 3), the automorphy of their constant terms on the Levi factors (Lemma 4), the choice, for the given irreducible subquotient, of a generator on which the centre $Z_M(\mathbb{A})$ of the Levi factor acts by a character $\chi$ (Lemma 6)
- [Weighted cuspidal spectrum with a fixed central character](weighted-cuspidal-spectrum-with-a-fixed-central-character.md), for the decomposition into irreducible invariant subspaces of the cuspidal Hilbert space of the Levi factor with the automorphic central character $\chi$ of $Z_M(\mathbb{A})$, weighted by $\nu^{-2}$, and for the choice of a suitable component $H$ and submodule $V_1$ of $V$, with the kernel of the projection on $V_1$ contained in $U$ (a nonzero projection of a slice of the generator is not enough), which realizes the subquotient as a quotient of a module of the global Hecke algebra inside $\mathrm{Ind}(\delta_P^{-1/2} \sigma)$, in the "only if" direction (Langlands, pp. 3–4); it comes after the discreteness of the cuspidal spectrum
- [Harish-Chandra's finiteness theorem for automorphic forms](harish-chandra-finiteness-theorem.md), for the admissibility of the representations generated by constant terms of automorphic forms, which are automorphic forms on $M(\mathbb{A})$ by the previous node

## Sources

- R. P. Langlands, "On the notion of an automorphic representation", Proc. Sympos. Pure Math. 33,
  Part 1, 1979, 203–207,
  <https://sunsite.ubc.ca/DigitalMathArchive/Langlands/pdf/notion-ps.pdf>: the paragraph before Lemma 1,
  Lemma 1 with its proof (using that $\mathrm{Ind}\, \sigma_v$ has a finite composition series),
  Proposition 2 ("The proof that every constituent of $\mathrm{Ind}\, \sigma$ is an automorphic representation
  will invoke the theory of Eisenstein series"), Lemmas 3–5 and the proof of Proposition 2.
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 9, §8, the
  statement of Langlands's theorem for $\mathrm{GL}_n$ ("If $\pi$ is any irreducible automorphic
  representation of $\mathrm{GL}_n(\mathbb{A})$ then there exists a partition $n = n_1 + \dots + n_r$ ... such that
  $\pi$ is a constituent of the induced representation", "a consequence of the theory of Eisenstein
  series").
