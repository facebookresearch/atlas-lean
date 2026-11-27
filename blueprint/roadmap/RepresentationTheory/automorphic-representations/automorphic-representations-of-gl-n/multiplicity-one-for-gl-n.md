# Multiplicity one for GLₙ

Let $k$ be a number field and $\pi$ an irreducible admissible representation of $\mathrm{GL}_n(\mathbb{A})$
(of the global Hecke algebra in the $K$-finite setting, or a smooth one in the smooth setting). Then $\pi$
occurs at most once in the space of cusp forms on $\mathrm{GL}_n(\mathbb{A})$: if $V_1$ and $V_2$ are
subspaces of cusp forms, each invariant and isomorphic to $\pi$, then $V_1 = V_2$. For a unitary central
character $\omega$, the multiplicities in
$L^2_0(\omega) = \widehat{\bigoplus}_\pi m(\pi) V_\pi$ given by the
[discreteness of the cuspidal spectrum](../automorphic-forms-on-reductive-groups/discreteness-of-the-cuspidal-spectrum.md)
are therefore $m(\pi) \le 1$.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cusp forms and cuspidal automorphic representations
- [Discreteness of the cuspidal spectrum](../automorphic-forms-on-reductive-groups/discreteness-of-the-cuspidal-spectrum.md), for the multiplicities $m(\pi)$

## Proof depends on

- [Fourier expansion and global Whittaker models of cusp forms on GLₙ](whittaker-fourier-expansion.md), for the global uniqueness of Whittaker functionals, which makes the two Whittaker functionals $\varphi_i \mapsto W_{\varphi_i}(e)$ proportional, and for the Fourier expansion, which recovers each cusp form from its Whittaker function
- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/whittaker-models-for-gl-n.md), for the uniqueness of local Whittaker models, used for multiplicity one

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 4, §3,
  Theorem 4.2 (Multiplicity One, "proven independently by Piatetski-Shapiro and Shalika, based on the
  Fourier expansion and the global uniqueness of Whittaker models") with its proof; Lecture 3, §4,
  Theorem 3.7.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states this result over totally complex fields as `GlobalTheory.Published.CuspidalMultiplicityOne`.
