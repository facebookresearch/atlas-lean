# Naturality of the periodicity isomorphisms of Tate cohomology for finite cyclic groups

Let $R$ be a commutative ring, $G$ a finite cyclic group and $\sigma$ a generator of $G$. For every
representation $A$ of $G$ over $R$ and every integer $n$ there is an isomorphism of $R$-modules

$$\theta^n_A \colon \hat H^n(G, A) \to \hat H^{n+2}(G, A),$$

determined by $\sigma$, such that for every morphism of representations $f \colon A \to B$

$$\hat H^{n+2}(G, f) \circ \theta^n_A = \theta^n_B \circ \hat H^n(G, f).$$

This strengthens the [periodicity of Tate cohomology](nonempty-periodicity-iso.md), which gives an
isomorphism for each representation separately. The isomorphism is the composite of two connecting
homomorphisms. Let $m$ be the order of $G$. Tensoring the exact sequence of free abelian groups

$$0 \to \mathbb{Z} \to \mathbb{Z}[G] \to \mathbb{Z}[G] \to \mathbb{Z} \to 0,$$

whose maps are $1 \mapsto \sum_{g \in G} g$, multiplication by $\sigma - 1$ and the augmentation, with
$A$ over $\mathbb{Z}$ gives an exact sequence $0 \to A \to \mathbb{Z}[G] \otimes A \to \mathbb{Z}[G] \otimes A \to A \to 0$,
functorial in $A$, whose middle terms have zero Tate cohomology. Splitting it into two short exact
sequences, the connecting homomorphisms of their long exact sequences of Tate cohomology are
isomorphisms $\hat H^n(G, A) \to \hat H^{n+1}(G, J) \to \hat H^{n+2}(G, A)$, with $J$ the image of the
middle map, and connecting homomorphisms commute with the maps induced by morphisms of short exact
sequences.

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter II, §3: Proposition 3.4 (the choice of a
  generator of a finite cyclic group $G$ determines isomorphisms $H^r_T(G, M) \to H^{r+2}_T(G, M)$ for all
  $G$-modules $M$ and all $r$) and its proof, which constructs them from the exact sequence above and the
  long exact sequence (22) of Tate cohomology; Proposition 3.1 (induced modules have zero Tate
  cohomology). Remark 3.5 there identifies the isomorphism with the cup product with the class in
  $H^2(G, \mathbb{Z})$ that corresponds to the homomorphism $G \to \mathbb{Q}/\mathbb{Z}$ sending
  $\sigma$ to $1/m$, citing J.-P. Serre, *Local Fields*, VIII, §4.
