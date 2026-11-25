# Jacquet–Shalika bounds on Satake parameters

Let $F$ be a non-archimedean local field with uniformizer $\varpi$ and residue field of order $q$.

1. **Local bound** (Jacquet–Shalika). Let $\pi$ be an irreducible unitary generic unramified
   representation of $\mathrm{GL}_n(F)$, $\pi \simeq \mathrm{Ind}(\mu_1 \otimes \dots \otimes \mu_n)$ with unramified
   characters $\mu_i$ of $F^\times$. Then its Satake parameters satisfy
   $q^{-1/2} < \lvert \mu_i(\varpi) \rvert < q^{1/2}$ for $1 \le i \le n$.
2. **Cuspidal representations.** Let $k$ be a number field and $\pi \simeq \bigotimes'_v \pi_v$ a unitary
   cuspidal automorphic representation of $\mathrm{GL}_n(\mathbb{A})$. At every finite place $v$ where $\pi_v$ is
   unramified, the Satake parameters $\alpha$ of $\pi_v$ satisfy $\mathrm{N}v^{-1/2} < \lvert \alpha \rvert < \mathrm{N}v^{1/2}$.

## Depends on

- [Tempered and unitary representations of GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/tempered-and-unitary-representations-of-gl-n.md), for unitary representations of $\mathrm{GL}_n(F)$
- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/whittaker-models-for-gl-n.md), for generic representations
- [Borel–Casselman theorem on Iwahori-fixed vectors](../../reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/borel-casselman-theorem.md), for unramified representations as constituents of unramified principal series
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_v$

## Proof depends on

- [Rankin–Selberg L-functions for GLₙ × GLₘ](rankin-selberg-l-functions-for-gl-n.md), for the unramified computation $\Psi(s, W^\circ, \bar W^\circ, \Phi^\circ) = \det(1 - q^{-s} A_\pi \otimes \bar A_\pi)^{-1}$ applied to $\pi$ and its complex conjugate, and for the absolute convergence of this local integral for $\operatorname{Re} s \ge 1$ when $\pi$ is unitary and generic; the factor $1 - \lvert \mu_i(\varpi) \rvert^2 q^{-s}$ of the determinant then cannot vanish for $\operatorname{Re} s \ge 1$, and the same argument for $\tilde\pi$ gives the lower bound
- [Fourier expansion and global Whittaker models of cusp forms on GLₙ](whittaker-fourier-expansion.md), for the genericity of the local components of a cuspidal representation, used in item 2
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the unitarity of the local components of a unitary cuspidal representation, used in item 2
- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/whittaker-models-for-gl-n.md), for the description of generic irreducible representations by unlinked segments, from which a generic unramified representation is the full, irreducible, unramified principal series $\mathrm{Ind}(\mu_1 \otimes \dots \otimes \mu_n)$, the form in which items 1 and 2 are stated (Cogdell, Lecture 7)

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 7, §1, p. 54 (an
  irreducible generic unramified representation is a full induced representation from unramified
  characters), Theorem 7.1,
  Corollary 7.1.2 ("the Jacquet-Shalika bounds on the Satake parameters", $q^{-1/2} < \lvert \mu_i(\varpi) \rvert < q^{1/2}$)
  and its proof; Lecture 4, Corollary 4.1.2; Lecture 3, Theorem 3.6.
- P. Sarnak, "Notes on the generalized Ramanujan conjectures", in *Harmonic Analysis, the Trace Formula,
  and Shimura Varieties*, Clay Math. Proc. 4, American Mathematical Society, 2005, 659–685,
  <https://www.claymath.org/library/proceedings/cmip04c.pdf>: §1, the paragraph before (11) (the local
  components of a cuspidal representation are unitary and generic), (11) (Jacquet and Shalika: analyticity
  of $L(s, \pi_v \times \tilde\pi_v)$ in $\operatorname{Re} s > 1$) and (12) ($\lvert \log_{\mathrm{N}(v)} \lvert \alpha_j(\pi_v) \rvert \rvert < \tfrac12$
  at unramified finite places).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states item 2 over totally complex fields as `GlobalTheory.Published.JacquetShalikaBound`, a component of
  `GlobalTheory.Published.JacquetShalika`.
