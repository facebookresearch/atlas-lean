# Parabolic induction and Jacquet functors

Let $F$ be a non-archimedean local field and $G = \mathbf{G}(F)$ for a connected reductive group
$\mathbf{G}$ over $F$. Fix a minimal parabolic subgroup $P_0$ of $G$ and a maximal split torus
$A_0 \subset P_0$. For a parabolic subgroup $P \supseteq P_0$ with unipotent radical $U$, let $M$
be the unique Levi subgroup of $P$ containing $A_0$, so that $P = MU$ and $M \cap U = \{e\}$;
such an $M$ is a **standard Levi subgroup** of $G$, written $M < G$, and it determines $P$ and
$U$. Let $\delta_P(m)$, for $m \in M$, be the module of the automorphism $u \mapsto m u m^{-1}$ of
$U$, so that $d(m u m^{-1}) = \delta_P(m)\, du$ for a Haar measure $du$ on $U$; it equals
$\lvert \det (\mathrm{Ad}(m)|_{\mathrm{Lie}\, U}) \rvert_F$.

- **Normalized parabolic induction** $i_{G,M} \colon \mathrm{Alg}\, M \to \mathrm{Alg}\, G$: for a
  smooth representation $(\rho, L)$ of $M$, $i_{G,M}(\rho)$ is the representation of $G$ by right
  translation on the space of functions $f \colon G \to L$ such that
  $f(umg) = \delta_P(m)^{1/2}\rho(m) f(g)$ for $u \in U$, $m \in M$, $g \in G$, and such that $f$
  is right invariant under some open subgroup of $G$.
- **Normalized Jacquet functor** $r_{M,G} \colon \mathrm{Alg}\, G \to \mathrm{Alg}\, M$: for a
  smooth representation $(\pi, E)$ of $G$, let $E(U)$ be the span of the vectors
  $\pi(u)\xi - \xi$ ($u \in U$, $\xi \in E$); then $r_{M,G}(\pi)$ is the representation
  $m \mapsto \delta_P(m)^{-1/2}\pi(m)$ of $M$ on the space $E_U = E/E(U)$ of $U$-coinvariants.

For $G = \mathrm{GL}_n(F)$, with $P_0$ the upper triangular and $A_0$ the diagonal matrices, the
standard Levi subgroups are the block-diagonal subgroups
$\mathrm{GL}_{n_1}(F) \times \dots \times \mathrm{GL}_{n_r}(F)$ attached to the ordered partitions
$(n_1, \dots, n_r)$ of $n$, with $P$ the block upper triangular matrices.

**Theorem.** Let $N < M < G$ be standard Levi subgroups.

1. The functors $i_{G,M}$ and $r_{M,G}$ are exact.
2. $r_{M,G}$ is left adjoint to $i_{G,M}$ (Frobenius reciprocity): there are isomorphisms
   $\mathrm{Hom}_M(r_{M,G}(\pi), \rho) \cong \mathrm{Hom}_G(\pi, i_{G,M}(\rho))$, natural in
   $\pi \in \mathrm{Alg}\, G$ and $\rho \in \mathrm{Alg}\, M$.
3. $i_{G,M} \circ i_{M,N} \cong i_{G,N}$ and $r_{N,M} \circ r_{M,G} \cong r_{N,G}$.
4. $i_{G,M}(\tilde\rho) \cong i_{G,M}(\rho)^\sim$ for $\rho \in \mathrm{Alg}\, M$.
5. Both functors carry admissible representations to admissible ones (for $r_{M,G}$ this is a
   theorem of Jacquet), and $r_{M,G}$ carries finitely generated representations to finitely
   generated ones.
6. **Jacquet's surjectivity theorem.** Let $(\pi, E)$ be an admissible representation of $G$,
   $\bar U$ the unipotent radical of the parabolic subgroup opposite to $P$ with respect to $M$, and
   $K_0$ a compact open subgroup of $G$ with an Iwahori factorization
   $K_0 = (K_0 \cap \bar U)(K_0 \cap M)(K_0 \cap U)$. Then the projection $E \to E_U$ maps the
   $K_0$-fixed vectors $E^{K_0}$ onto the $(K_0 \cap M)$-fixed vectors $(E_U)^{K_0 \cap M}$. Since
   such subgroups $K_0$ form a basis of neighbourhoods of the identity, this gives the admissibility
   of $r_{M,G}(\pi)$ in item 5.

## Depends on

- [Smooth and admissible representations of p-adic groups](smooth-representations-of-p-adic-groups.md)
- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for minimal and standard parabolic subgroups, maximal split tori, Levi decompositions, opposite parabolic subgroups and compact open subgroups with an Iwahori factorization

## Proof depends on

- [Parabolic subgroups, Bruhat–Tits buildings and Moy–Prasad filtrations](parabolic-subgroups-buildings-and-moy-prasad-filtrations.md), for the compactness of $G/P$, the unimodularity of $G$ and the existence of a basis of neighbourhoods of the identity consisting of compact open subgroups with an Iwahori factorization, used in item 6 and in Jacquet's admissibility theorem

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.7 (modules of automorphisms), §1.8
  (the functors $I_{U,\theta}$, $i_{U,\theta}$ and $r_{U,\theta}$, with the factors
  $\mathrm{mod}_U^{\pm 1/2}$), Proposition 1.9, §2.1 (standard Levi subgroups), §2.2 (the example of
  $\mathrm{GL}_n$) and Proposition 2.3 (a)–(e), whose proof reads: "It was proved by Jacquet that
  $r_{M,G}$ carries admissible representations into admissible ones".
- W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive
  groups*, notes, draft of 1 May 1995, <https://personal.math.ubc.ca/~cass/research/pdf/p-adic-book.pdf>:
  §1.5 (modulus character), Theorem 3.3.1 (Jacquet modules of finitely generated, respectively
  admissible, representations; "the original result leading to it is Jacquet's", with a proof due
  to Borel) and Theorem 3.3.3 (item 6: "Let $(\pi, V)$ be an admissible representation of G, $K_0$
  a compact open subgroup of G with an Iwahori factorization $K_0 = N_0^- M_0 N_0$ with respect to
  P. Then the canonical projection from $V^{K_0}$ to $V_N^{M_0}$ is surjective").
- A. Moy and G. Prasad, "Jacquet functors and unrefined minimal K-types", Comment. Math. Helv. 71
  (1996), 98–121, <https://doi.org/10.5169/seals-53837>: §2.1 and Theorem 2.2 (item 6, "a
  fundamental theorem of Jacquet and Harish-Chandra", with the consequence that the Jacquet module
  of an admissible representation is admissible).
- A. V. Zelevinsky, "Induced representations of reductive p-adic groups. II. On irreducible
  representations of GL(n)", Ann. Sci. École Norm. Sup. (4) 13 (1980), 165–210,
  <http://www.numdam.org/item?id=ASENS_1980_4_13_2_165_0>: §1.1 (the statement for
  $\mathrm{GL}_n$, with block-diagonal standard Levi subgroups).
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2): (2.2.1) (normalized induction from block upper triangular
  parabolic subgroups, with $\delta(m) = \lvert \det(\mathrm{Ad}_{U}(m)) \rvert$).
