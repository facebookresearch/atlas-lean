# Differents of completions and the local factorization of the norm of the different

This node is still to be broken down. It covers the comparison of the global different with the differents of the
completions that the self-dual measures on the adeles use. Let $K$ be a number field with ring of integers $\mathcal{O}_K$
and different $\mathfrak{d}_K$, and for a finite place $v$ above $p$ let $\mathcal{O}_v$ be the completion and $\mathfrak{d}_v$ the different of
$\mathcal{O}_v$ over $\mathbb{Z}_p$.

- **Completion.** $\mathfrak{d}_K \mathcal{O}_v = \mathfrak{d}_v$ for every finite place $v$: the different commutes with completion.
- **Norms.** Consequently $N(\mathfrak{d}_K) = \prod_v N(\mathfrak{d}_v)$, the product over the finite places of $\#(\mathcal{O}_v/\mathfrak{d}_v)$, and
  $\lvert d_K \rvert = N(\mathfrak{d}_K)$.
- **Self-dual measures.** For the standard additive character, the self-dual Haar measure on $K_v$ gives $\mathcal{O}_v$ the volume
  $N(\mathfrak{d}_v)^{-1/2}$.

## Expansion

A good expansion has statement pages for the compatibility of the different with completion, for the factorization of its
norm and for the self-dual volume of $\mathcal{O}_v$, each citing the sources below with locators. The compatibility with
completion is proved through trace duals: the trace dual of $\mathcal{O}_K \otimes \mathbb{Z}_p$ in $K \otimes \mathbb{Q}_p = \prod_{v \mid p} K_v$ is
$\mathcal{O}_K^* \otimes \mathbb{Z}_p$, and since $\mathcal{O}_K \otimes \mathbb{Z}_p \cong \prod_{v \mid p} \mathcal{O}_v$ it splits as the product of the trace duals of
the $\mathcal{O}_v$, so that the inverse different
$\mathcal{O}_K^*$ generates each $\mathcal{O}_v^*$. The compatibility with localization, which the pages linked below state, is the
corresponding step for localization only. The equality $\lvert d_K \rvert = N(\mathfrak{d}_K)$ comes from the discriminant ideal,
the ideal of norms of the elements of the different, and its absolute norm $\lvert d_K \rvert$.

## Depends on

- [The different commutes with localization](map-different-ideal-eq-localization-of-f.md), for the different and its compatibility with localization, a step toward the compatibility with completion

## Proof depends on

- [The norm of the different commutes with localization](map-span-norm-different-ideal-eq-localiz.md), for the localization of the norm of the different, a step toward the local factorization of the norm
- [The discriminant ideal is the norm of the different](discriminant-ideal-eq-span-norm.md), for the discriminant ideal as the ideal of norms of the elements of the different
- [Absolute norm of the discriminant ideal of a number field](../../../NumberTheory/algebraic-number-theory/discriminants-ramification/discriminants-of-number-fields/abs-norm-discriminant-ideal.md), for $\lvert d_K \rvert$ as the absolute norm of the discriminant ideal
- [Base change to a finite completion as a product of completions](../../../NumberTheory/algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/the-finite-place-completion-tensor-product/completion-tensor-product-alg-equiv.md), for the decomposition $\mathbb{Q}_p \otimes_{\mathbb{Q}} K \cong \prod_{v \mid p} K_v$ of the field factor (its case of the extension $K/\mathbb{Q}$), on which Sutherland's trace-dual argument computes the trace pairing
- [Base change of the ring of integers to a finite completion](../../../NumberTheory/algebraic-number-theory/discriminants-ramification/completions-of-number-fields-at-finite-places/the-finite-place-completion-tensor-product/ring-of-integers-completion-tensor-product.md), for the integral decomposition $\mathbb{Z}_p \otimes_{\mathbb{Z}} \mathcal{O}_K \cong \prod_{v \mid p} \mathcal{O}_v$ (its case of the extension $K/\mathbb{Q}$), which identifies the lattice whose trace dual is computed; the field decomposition alone does not identify it

## Sources

- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: Proposition 4.8, p. 16 (the self-dual Haar measure gives $\mathcal{O}$ the volume $(N\mathcal{D})^{-1/2}$, $\mathcal{D}$ the different of
  $F/F_0$), and §5.3, Proposition 5.5 and its proof, p. 28 (the volume of $\mathbb{A}/K$ through the covolume of $\mathcal{O}_K$ and the norm
  of the different).
- A. V. Sutherland, 18.785 Number theory I, Fall 2021, Lecture 11, "Totally ramified extensions and Krasner's lemma",
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes11.pdf>: Theorem 11.23 (5), p. 8, with its proof through p. 9
  ($L \otimes_K K_{\mathfrak{p}} \cong \prod_{\mathfrak{q} \mid \mathfrak{p}} L_{\mathfrak{q}}$), and Corollary 11.26, p. 10 ($B \otimes_A \hat A_{\mathfrak{p}} \cong \prod_{\mathfrak{q} \mid \mathfrak{p}} \hat B_{\mathfrak{q}}$ as
  $\hat A_{\mathfrak{p}}$-algebras).
- A. V. Sutherland, 18.785 Number theory I, Fall 2021, Lecture 12, "The different and the discriminant",
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes12.pdf>: Proposition 12.3 (the different respects localization)
  and Proposition 12.4 with its proof, p. 2 (the different respects completion, $D_{\hat B_q / \hat A_p} = D_{B/A} \hat B_q$, through
  the trace pairing on $L \otimes K_p \cong \prod_{q \mid p} L_q$).
- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter III, §2 (the different, its local
  description and $\lvert d_K \rvert = N(\mathfrak{d}_K)$).
