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
norm and for the self-dual volume of $\mathcal{O}_v$, each citing the sources below with locators; the compatibility with
localization, which the pages linked below state, reduces the first to the complete local case.

## Depends on

- [The different commutes with localization](map-different-ideal-eq-localization-of-f.md), for the different and its localization

## Proof depends on

- [The norm of the different commutes with localization](map-span-norm-different-ideal-eq-localiz.md), for the localization step

## Sources

- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: Proposition 4.8, p. 16 (the self-dual Haar measure gives $\mathcal{O}$ the volume $(N\mathcal{D})^{-1/2}$, $\mathcal{D}$ the different of
  $F/F_0$), and §5.3, Proposition 5.5 and its proof, p. 28 (the volume of $\mathbb{A}/K$ through the covolume of $\mathcal{O}_K$ and the norm
  of the different).
- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter III, §2 (the different, its local
  description and $\lvert d_K \rvert = N(\mathfrak{d}_K)$).
