# Rankin–Selberg L-functions for GLₙ × GLₘ

This node is still to be broken down. It covers the Rankin–Selberg theory of Jacquet, Piatetski-Shapiro
and Shalika for pairs of cuspidal automorphic representations of $\mathrm{GL}_n(\mathbb{A})$ and
$\mathrm{GL}_m(\mathbb{A})$ over a number field $k$, globally and at the places that the
[non-archimedean local theory](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md)
does not treat.

- **Global Eulerian integrals.** For cusp forms $\varphi \in \pi$, $\varphi' \in \pi'$ and $m < n$ the
  integrals $I(s, \varphi, \varphi')$ of $\varphi$ projected to the mirabolic subgroup against $\varphi'$, and for
  $m = n$ the integrals $I(s, \varphi, \varphi', \Phi)$ against the Eisenstein series $E(g, \Phi, s)$ built from a
  Schwartz–Bruhat function $\Phi$ on $\mathbb{A}^n$; their convergence, meromorphy and poles, their
  functional equations, and their unfolding, through the
  [Fourier expansion](whittaker-fourier-expansion.md), into Euler products of local integrals of Whittaker
  functions.
- **The unramified computation.** For unramified $\pi_v$, $\pi'_v$ and $\psi_v$, the local integral of the
  normalized spherical Whittaker functions equals $L(s, \pi_v \times \pi'_v) = \det(1 - q_v^{-s} A_{\pi_v} \otimes A_{\pi'_v})^{-1}$,
  with $A_{\pi_v}$ the Satake parameters, and $\varepsilon(s, \pi_v \times \pi'_v, \psi_v) = 1$.
- **Archimedean theory.** Convergence of the local integrals for $\operatorname{Re} s \gg 0$ and, for unitary
  generic representations, for $\operatorname{Re} s \ge 1$ at every place; meromorphic continuation, local
  functional equations and the archimedean $L$-factors defined through the Langlands parameters.
- **Local factors at the removed places.** For unitary generic $\pi_v$, $\pi'_v$, the local factor
  $L(s, \pi_v \times \pi'_v)$ is $P_v(q_v^{-s})^{-1}$ for a polynomial with $P_v(0) = 1$ at a finite place and a product of
  $\Gamma$-factors at an infinite place, hence never zero, and it has no pole in $\operatorname{Re} s \ge 1$: at a finite place,
  and at an infinite place when $m = n$ or $m = n - 1$, it is a finite sum of local integrals that converge there
  (Cogdell, Theorem 8.5); for lower ranks at an infinite place one uses instead that for each $s_1$ some
  normalized local integral is non-zero at $s_1$ (Cogdell, Corollary 8.3.2), a uniform finite sum of ordinary
  integrals not being known.
- **Global $L$-functions.** For cuspidal $\pi$, $\pi'$ the completed $L$-function is the product over all places,
  archimedean ones included, $L(s, \pi \times \pi') = \prod_v L(s, \pi_v \times \pi'_v)$, and
  $\varepsilon(s, \pi \times \pi') = \prod_v \varepsilon(s, \pi_v \times \pi'_v, \psi_v)$, independent of $\psi$. For unitary cuspidal
  $\pi$, $\pi'$, the partial product $L^S(s, \pi \times \pi')$ over the places outside a finite set $S$ converges
  absolutely for $\operatorname{Re} s > 1$, and does not vanish there (on $\operatorname{Re} s = 1$ it need not converge: for $n = m = 1$
  and trivial characters it is a partial Dedekind zeta function, with a pole at $s = 1$). If $m < n$,
  $L(s, \pi \times \pi')$ is entire, bounded in vertical strips and satisfies
  $L(s, \pi \times \pi') = \varepsilon(s, \pi \times \pi') L(1 - s, \tilde\pi \times \tilde\pi')$. If $m = n$, it is meromorphic, with
  simple poles exactly at the points $s = i\sigma$ and $s = 1 + i\sigma$, $\sigma \in \mathbb{R}$, such that
  $\tilde\pi \simeq \pi' \otimes \lvert \det \rvert^{i\sigma}$, and entire if there is no such $\sigma$; it is bounded in vertical strips
  away from its poles and satisfies the same functional equation. In particular $L(s, \pi \times \tilde\pi)$ has a
  simple pole at $s = 1$, and so does $L^S(s, \pi \times \tilde\pi)$.
- **Non-vanishing on the line $\operatorname{Re} s = 1$** (Shahidi). For unitary cuspidal $\pi$, $\pi'$ and a finite set $S$ of places
  containing the archimedean places and those where $\pi$ or $\pi'$ ramifies, the partial
  $L$-function $L^S(s, \pi \times \pi')$ does not vanish on $\operatorname{Re} s = 1$, except that it has a pole at the points
  $1 + i\sigma$ with $\tilde\pi \simeq \pi' \otimes \lvert \det \rvert^{i\sigma}$.

A good expansion has pages for the global integrals in the cases $m < n$ and $m = n$ (with the mirabolic
Eisenstein series), for their unfolding to Euler products, for the unramified computation, for the
archimedean local theory, for the global theorems on $L(s, \pi \times \pi')$, and for Shahidi's non-vanishing on
$\operatorname{Re} s = 1$, each with a precise
statement and the sources below with locators, and with the original papers (Jacquet, Piatetski-Shapiro
and Shalika, Amer. J. Math. 105 (1983); Jacquet and Shalika, Amer. J. Math. 103 (1981); Jacquet, "Archimedean
Rankin–Selberg integrals", 2009) consulted for hypotheses.

## Depends on

- [Fourier expansion and global Whittaker models of cusp forms on GLₙ](whittaker-fourier-expansion.md), for Whittaker functions and the genericity of local components
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md), for the local factors at the finite places
- [Whittaker models for GLₙ over archimedean fields](archimedean-whittaker-models-for-gl-n.md), for Whittaker models at the infinite places
- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the Eisenstein series used when $m = n$
- [Rapid decay of cusp forms](../automorphic-forms-on-reductive-groups/rapid-decay-of-cusp-forms.md), for the convergence of the global integrals
- [Poisson summation formula for adeles](../../../NumberTheory/algebraic-number-theory/adeles-class-field-theory/adelic-poisson-summation.md), for the functional equation of the mirabolic Eisenstein series $E(g, \Phi, s)$ used when $m = n$ (Cogdell, Proposition 5.4)

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 5 (Propositions
  5.1–5.5: the global integrals for $m < n$ and $m = n$, the mirabolic Eisenstein series), Lecture 6
  (Propositions 6.1–6.7: the non-archimedean local theory, including convergence for $\operatorname{Re} s \ge 1$ in
  Proposition 6.2 (i)), Lecture 7 (Theorem 7.1, Corollaries 7.1.1 and 7.1.2: the unramified computation),
  Lecture 8 (Propositions 8.1–8.3, Theorems 8.1–8.4: the archimedean theory; Theorem 8.5, p. 66, finite sums
  of integrals for $m = n$ or $m = n - 1$, and Corollary 8.3.2, non-zero normalized integrals), Lecture 9 (Definition 9.1, the
  completed $L$-function over all places; Theorems 9.1 and 9.2, the global $L$-functions, with the simple
  poles of Theorem 9.2 (i); §5, boundedness in vertical strips, with Gelbart and Shahidi, J. Amer. Math. Soc.
  14 (2001); §7, the local factors at the places of $S$: never zero, and without poles in $\operatorname{Re} s \ge 1$).
- H. Jacquet and J. A. Shalika, "On Euler products and the classification of automorphic representations
  I", Amer. J. Math. 103 (1981), 499–558, <https://doi.org/10.2307/2374103>: Theorem (5.3) (absolute
  convergence and non-vanishing of the partial Euler product for unitary cuspidal $\pi$, $\pi'$ in $\operatorname{Re} s > 1$).
- H. Jacquet and J. A. Shalika, "On Euler products and the classification of automorphic forms II", Amer. J.
  Math. 103 (1981), 777–815: §3.7, p. 804 (non-vanishing on $\operatorname{Re} s = 1$ away from the poles, attributed to
  F. Shahidi, "On certain L-functions", Amer. J. Math. 103 (1981), 297–356).
