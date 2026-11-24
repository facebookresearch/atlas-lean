# Strong multiplicity one for GLₙ

Let $k$ be a number field and $\pi_1 \simeq \bigotimes'_v \pi_{1,v}$, $\pi_2 \simeq \bigotimes'_v \pi_{2,v}$ two
cuspidal automorphic representations of $\mathrm{GL}_n(\mathbb{A})$, realized in the space of cusp forms
and decomposed by the
[tensor product theorem](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md). If there is
a finite set $S$ of places with $\pi_{1,v} \simeq \pi_{2,v}$ for all $v \notin S$, then $\pi_1$ and $\pi_2$ are
equal as spaces of cusp forms.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](../automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cuspidal automorphic representations
- [Tensor product theorem for automorphic representations](../automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_{i,v}$

## Proof depends on

- [Rankin–Selberg L-functions for GLₙ × GLₘ](rankin-selberg-l-functions-for-gl-n.md), for the following (the first two steps are not Rankin–Selberg results: the ratio of the central characters is a character of $\prod_{v \in S} k_v^\times$ trivial on the diagonally embedded $k^\times$, hence trivial by weak approximation, Cogdell, Lecture 4, §4, step (iii), p. 35; and the same twist by a real power of $\lvert \det \rvert$ then makes both representations unitary, Cogdell, p. 26): then $L(s, \pi_1 \times \tilde\pi_2)$ has a pole at $s = 1$ exactly when $\pi_1 \simeq \pi_2$ (the actual simple pole of the completed $L$-function), the local factors at the places of $S$ have neither zeros nor poles in $\operatorname{Re} s \ge 1$, and $L^S(s, \pi_1 \times \tilde\pi_2) = L^S(s, \pi_1 \times \tilde\pi_1)$ has a pole at $s = 1$
- [Multiplicity one for GLₙ](multiplicity-one-for-gl-n.md), which turns $\pi_1 \simeq \pi_2$ into the equality of the spaces of cusp forms

## Sources

- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in
  *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American Mathematical Society,
  2004; author's version <https://people.math.osu.edu/cogdell.1/fields-www.pdf>: Lecture 4, §4,
  Theorem 4.3 (Strong Multiplicity One, "originally due to Piatetski-Shapiro", with his proof through the
  Kirillov model, which needed $S$ to consist of finite places; the theorem itself holds for any finite
  $S$); Lecture 9, §7, Theorem 9.3 and the proof of Jacquet and Shalika through $L(s, \pi_1 \times \tilde\pi_2)$
  ("Without loss of generality we may assume $\pi_1$ and $\pi_2$ are unitary").
