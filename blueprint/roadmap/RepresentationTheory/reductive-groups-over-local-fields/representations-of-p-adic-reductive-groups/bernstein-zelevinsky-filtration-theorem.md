# The Bernstein–Zelevinsky filtration of a restriction of an induced representation

This node is still to be broken down. It covers Bernstein and Zelevinsky's Theorem 5.2 (1977), which computes a
restriction functor applied to an induction functor, with characters, and of which the geometric lemma for
parabolic induction is the case of trivial characters. Let $G$ be an $\ell$-group, countable at infinity, with
closed subgroups $P = M \ltimes U$ and $Q = N \ltimes V$, $U$ and $V$ limits of compact subgroups, and characters
$\theta$ of $U$ and $\psi$ of $V$ normalized by $M$ and $N$; let $i_{U,\theta} \colon \mathrm{Alg}\, M \to \mathrm{Alg}\, G$
and $r_{V,\psi} \colon \mathrm{Alg}\, G \to \mathrm{Alg}\, N$ be the normalized induction and restriction functors of
Bernstein and Zelevinsky ([smooth representations](l-spaces-distributions-and-smooth-representations-of-l-groups.md)).

- **Theorem.** Suppose that $Q$ has finitely many orbits on $X = P \backslash G$, numbered $Z_1, \dots, Z_k$ so that each
  $Z_1 \cup \dots \cup Z_i$ is open, and that for each orbit, with $w \in G$ such that $Pw^{-1} \in Z$, the subgroups
  $w(P), w(M), w(U)$ are decomposable with respect to $(N, V)$ and $w^{-1}(Q), w^{-1}(N), w^{-1}(V)$ with respect
  to $(M, U)$. Then $F = r_{V,\psi} \circ i_{U,\theta}$ has a filtration $0 = F_0 \subset F_1 \subset \dots \subset F_k = F$
  with $F_i / F_{i-1} \cong \Phi_{Z_i}$, where $\Phi_Z$ is zero unless $w(\theta)$ and $\psi$ agree on $w(U) \cap V$,
  and is otherwise the composition of a restriction functor of $M$ to $M' = M \cap w^{-1}(N)$, the conjugation by
  $w$, a twist by an explicit modulus character, and an induction functor from $N' = w(M')$ to $N$.

## Expansion

A good expansion has a statement page for the theorem, with the functors $\Phi_Z$ written out as in Bernstein and
Zelevinsky's §5.1, citing the source below with locators; they prove it through the filtration of the induced space by
the functions supported on the open sets $P(Z_1 \cup \dots \cup Z_i)$, an $\ell$-sheaf argument.

## Depends on

- [ℓ-spaces, distributions and smooth representations of ℓ-groups](l-spaces-distributions-and-smooth-representations-of-l-groups.md), for $\ell$-groups and the
  category $\mathrm{Alg}$

## Proof depends on

- [ℓ-spaces, distributions and smooth representations of ℓ-groups](l-spaces-distributions-and-smooth-representations-of-l-groups.md), for the exact sequences of
  Schwartz–Bruhat functions along the orbit filtration

## Sources

- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §1.8 (the functors $i_{U,\theta}$ and $r_{U,\theta}$), §5.1 (conditions (1)–(4) and the functors
  $\Phi_Z$), Theorem 5.2, p. 460, and §§5.3–5.4 (its proof by $\ell$-sheaves); §6.4 (the geometric lemma as the
  case of trivial characters).
