# The Bernstein–Zelevinsky filtration of a restriction of an induced representation

This node is still to be broken down. It covers Bernstein and Zelevinsky's Theorem 5.2 (1977), which computes a
restriction functor applied to an induction functor, with characters, and of which the geometric lemma for
parabolic induction is the case of trivial characters. Let $G$ be an $\ell$-group, countable at infinity, with
closed subgroups $M, U, N, V$ and closed subgroups $P = MU$ and $Q = NV$, where $M$ normalizes $U$, $N$ normalizes $V$ and $M \cap U = N \cap V = \{e\}$, $U$ and
$V$ limits of compact subgroups, and characters $\theta$ of $U$ and $\psi$ of $V$ normalized by $M$ and $N$. Write
$\mathrm{Alg}\, H$ for the category of smooth representations of an $\ell$-group $H$
([smooth representations](l-spaces-distributions-and-smooth-representations-of-l-groups.md)). For $g$ normalizing $U$, $\mathrm{mod}_U(g)$ is the
module of the automorphism $u \mapsto g u g^{-1}$ of $U$, defined by $d(g u g^{-1}) = \mathrm{mod}_U(g) \, du$ for a Haar measure $du$; it is a
character of the normalizer, distinct from the modular character of the group $U$ itself, which is trivial when $U$ is a
limit of compact subgroups.

- **The functors.** For $(\rho, L)$ in $\mathrm{Alg}\, M$, the normalized compact induction $i_{U,\theta}(\rho)$ is the representation of $G$
  by right translation on the functions $f \colon G \to L$ with $f(umg) = \theta(u)\, \mathrm{mod}_U(m)^{1/2} \rho(m) f(g)$ for $u \in U$,
  $m \in M$, $g \in G$, fixed under right translation by some open subgroup, and compactly supported modulo $P$; without the
  support condition it is the induction $I_{U,\theta}(\rho)$. For $(\pi, E)$ in $\mathrm{Alg}\, G$, the localization
  $r_{U,\theta}(\pi)$ is the representation of $M$ on the twisted coinvariants $E / E(U, \theta)$, where $E(U, \theta)$ is spanned by
  the vectors $\pi(u)\xi - \theta(u)\xi$, with $m$ acting by $\mathrm{mod}_U(m)^{-1/2} \pi(m)$. The functors $I_{U,\theta}$ and $i_{U,\theta}$ are exact,
  $r_{U,\theta}$ is exact because $U$ is a limit of compact subgroups, and $r_{U,\theta}$ is left adjoint to $I_{U,\theta}$.
- **Theorem.** A subgroup $H$ of $G$ is decomposable with respect to $(M, U)$ if $H \cap MU = (H \cap M)(H \cap U)$. Suppose that
  $Q$ has finitely many orbits on $X = P \backslash G$, numbered $Z_1, \dots, Z_k$ so that each $Z_1 \cup \dots \cup Z_i$ is open, and that
  for each orbit, with $w \in G$ such that $Pw^{-1} \in Z$, the subgroups $w(P), w(M), w(U)$ are decomposable with respect to
  $(N, V)$ and $w^{-1}(Q), w^{-1}(N), w^{-1}(V)$ with respect to $(M, U)$, where $w(g) = wgw^{-1}$. Then
  $F = r_{V,\psi} \circ i_{U,\theta}$ has a filtration $0 = F_0 \subset F_1 \subset \dots \subset F_k = F$ with $F_i / F_{i-1} \cong \Phi_{Z_i}$.
  Here $\Phi_Z$ is zero unless $w(\theta)$ and $\psi$ agree on $w(U) \cap V$, and is otherwise the composite of the localization
  of $M$ to $M' = M \cap w^{-1}(N)$ along $M \cap w^{-1}(V)$, the conjugation by $w$, a twist by an explicit product of modulus
  characters, and the normalized compact induction from $N' = w(M')$ to $N$ along $N \cap w(U)$.

## Expansion

A good expansion has definition pages for the functors $i_{U,\theta}$, $I_{U,\theta}$ and $r_{U,\theta}$ with their exactness and
adjunction, and a statement page for the theorem, with the functors $\Phi_Z$ written out as in Bernstein and Zelevinsky's
§5.1, citing the source below with locators. The proof filters the induced space by the functions supported on the
open sets $P(Z_1 \cup \dots \cup Z_i)$, an $\ell$-sheaf argument, and the exactness of $r_{V,\psi}$ makes the subquotients
$F_{Z_i}$ of this filtration (§§5.3–5.4); the identification of each $F_Z$ with $\Phi_Z$ takes the rest of the section,
§§5.5–5.17, through an explicit isomorphism given by an integral over $V \cap w(P) \backslash V$ and a reduction to free
representations.

## Depends on

- [ℓ-spaces, distributions and smooth representations of ℓ-groups](l-spaces-distributions-and-smooth-representations-of-l-groups.md), for $\ell$-groups and the
  category $\mathrm{Alg}$ of smooth representations

## Proof depends on

- [ℓ-spaces, distributions and smooth representations of ℓ-groups](l-spaces-distributions-and-smooth-representations-of-l-groups.md), for the exact sequences of
  Schwartz–Bruhat functions along the orbit filtration

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: p. 444 ($\mathrm{mod}_U$ on the normalizer of $U$, and the module of the group),
  §1.8, pp. 444–445 (the functors $I_{U,\theta}$, $i_{U,\theta}$ and $r_{U,\theta}$, with the factor $\mathrm{mod}_U^{1/2}$), §1.9, Proposition, p. 445 (exactness and adjunction), §5.1, pp. 459–460 (conditions
  (1)–(4), decomposable subgroups and the functors $\Phi_Z$), Theorem 5.2, p. 460, §§5.3–5.4, p. 461 (the filtration by
  $\ell$-sheaves, reducing the theorem to $F_Z \cong \Phi_Z$ for each orbit), §§5.5–5.17, pp. 461–467 (that isomorphism; "Theorem 5.2
  is proved", p. 467); §6.4 (the geometric lemma as the case of trivial characters).
