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
- **Global $L$-functions.** For unitary cuspidal $\pi$, $\pi'$: if $m < n$, $L(s, \pi \times \pi')$ is entire,
  bounded in vertical strips and satisfies $L(s, \pi \times \pi') = \varepsilon(s, \pi \times \pi') L(1 - s, \tilde\pi \times \tilde\pi')$;
  if $m = n$ it is meromorphic with at most simple poles at $s = i\sigma$ and $s = 1 + i\sigma$ where
  $\tilde\pi \simeq \pi' \otimes \lvert \det \rvert^{i\sigma}$, entire otherwise, bounded in vertical strips away from
  the poles, with the same functional equation.

A good expansion has pages for the global integrals in the cases $m < n$ and $m = n$ (with the mirabolic
Eisenstein series), for their unfolding to Euler products, for the unramified computation, for the
archimedean local theory, and for the global theorems on $L(s, \pi \times \pi')$, each with a precise
statement and the sources below with locators, and with the original papers (Jacquet, Piatetski-Shapiro
and Shalika, Amer. J. Math. 105 (1983); Jacquet and Shalika, Amer. J. Math. 103 (1981); Jacquet, "Archimedean
Rankin–Selberg integrals", 2009) consulted for hypotheses.

## Depends on

- [Fourier expansion and global Whittaker models of cusp forms on GLₙ](whittaker-fourier-expansion.md), for Whittaker functions and the genericity of local components
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](../../reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md), for the local factors at the finite places
- [Whittaker models for GLₙ over archimedean fields](archimedean-whittaker-models-for-gl-n.md), for Whittaker models at the infinite places
- [Eisenstein series and their meromorphic continuation](../automorphic-forms-on-reductive-groups/eisenstein-series.md), for the Eisenstein series used when $m = n$
- [Rapid decay of cusp forms](../automorphic-forms-on-reductive-groups/rapid-decay-of-cusp-forms.md), for the convergence of the global integrals

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 5 (Propositions
  5.1–5.5: the global integrals for $m < n$ and $m = n$, the mirabolic Eisenstein series), Lecture 6
  (Propositions 6.1–6.7: the non-archimedean local theory, including convergence for $\operatorname{Re} s \ge 1$ in
  Proposition 6.2 (i)), Lecture 7 (Theorem 7.1, Corollaries 7.1.1 and 7.1.2: the unramified computation),
  Lecture 8 (Propositions 8.1–8.3, Theorems 8.1–8.4: the archimedean theory), Lecture 9 (Theorems 9.1 and
  9.2, the global $L$-functions; §5, boundedness in vertical strips, with Gelbart and Shahidi, J. Amer.
  Math. Soc. 14 (2001)).
