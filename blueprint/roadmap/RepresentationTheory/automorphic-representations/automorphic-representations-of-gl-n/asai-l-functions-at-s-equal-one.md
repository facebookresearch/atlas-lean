# Asai L-functions at s = 1

This node is still to be broken down. It covers the two Asai $L$-functions of a cuspidal representation of
$\mathrm{GL}_N$ over a quadratic extension and their behaviour at $s = 1$, as the endoscopic classification of unitary
groups uses them. Let $E/F$ be a quadratic extension of number fields with nontrivial automorphism $c$, and $\varphi$
a unitary cuspidal automorphic representation of $\mathrm{GL}_N(\mathbb{A}_E)$.

- **Factorization.** The [Rankin–Selberg $L$-function](rankin-selberg-l-functions-for-gl-n.md) factors as
  $L(s, \varphi \times \varphi^c) = L(s, \varphi, \mathrm{Asai}^+)\, L(s, \varphi, \mathrm{Asai}^-)$, where the two Asai
  $L$-functions are those of the Asai representations $\mathrm{Asai}^\pm$ of the $L$-group, with
  $L(s, \varphi, \mathrm{Asai}^-) = L(s, \varphi \otimes \chi^-, \mathrm{Asai}^+)$ for a character $\chi^-$ of $\mathbb{A}_E^\times / E^\times$
  whose restriction to $\mathbb{A}_F^\times$ is the quadratic character of $E/F$.
- **Non-vanishing** (Shahidi). Both $L(s, \varphi, \mathrm{Asai}^\pm)$ are nonzero at $s = 1$. Consequently, if $\varphi$ is
  conjugate self-dual, so that $L(s, \varphi \times \varphi^c) = L(s, \varphi \times \varphi^\vee)$ has a simple pole at
  $s = 1$, exactly one of the two Asai $L$-functions has a pole at $s = 1$, and that pole is simple.

## Expansion

A good expansion has definition pages for the Asai representations and the Asai $L$-functions, with their local
factors after Goldberg, and statement pages for the factorization and for Shahidi's non-vanishing at $s = 1$, each citing
the sources below with locators.

## Depends on

- [Rankin–Selberg L-functions for GLₙ × GLₘ](rankin-selberg-l-functions-for-gl-n.md), for $L(s, \varphi \times \varphi^c)$ and its pole

## Proof depends on

- [Rankin–Selberg L-functions for GLₙ × GLₘ](rankin-selberg-l-functions-for-gl-n.md), for the simple pole of $L(s, \varphi \times \varphi^\vee)$ at $s = 1$

## Sources

- C. P. Mok, "Endoscopic classification of representations of quasi-split unitary groups", Mem. Amer. Math. Soc. 235
  (2015), no. 1108, arXiv:1206.0882 (version 5): §2.2, (2.2.9) (the Asai representations $\mathrm{Asai}^\pm$), and §2.5,
  (2.5.9), pp. 35–36 (the factorization of the Rankin–Selberg $L$-function, the local factors after Goldberg as special
  cases of Shahidi's, and, "by Shahidi's theorem [S]", the non-vanishing of both Asai $L$-functions at $s = 1$, whence
  exactly one has a simple pole there).
- D. Goldberg, "Some results on reducibility for unitary groups and local Asai L-functions", J. Reine Angew. Math. 448
  (1994), 65–95, and F. Shahidi, "A proof of Langlands' conjecture on Plancherel measures; complementary series for
  p-adic groups", Ann. of Math. 132 (1990), 273–330, as cited by Mok ([G], [S]).
