# Asai L-functions at s = 1

This node is still to be broken down. It covers the two Asai $L$-functions of a cuspidal representation of
$\mathrm{GL}_N$ over a quadratic extension and their behaviour at $s = 1$, as the endoscopic classification of unitary
groups uses them. Let $E/F$ be a quadratic extension of number fields with nontrivial automorphism $c$, and $\varphi$
a unitary cuspidal automorphic representation of $\mathrm{GL}_N(\mathbb{A}_E)$.

- **Factorization.** The [Rankin–Selberg $L$-function](rankin-selberg-l-functions-for-gl-n.md) factors as
  $L(s, \varphi \times \varphi^c) = L(s, \varphi, \mathrm{Asai}^+)\, L(s, \varphi, \mathrm{Asai}^-)$. Here the two Asai
  $L$-functions are those of the Asai representations $\mathrm{Asai}^\pm$ of the $L$-group
  $H = (\mathrm{GL}(V) \times \mathrm{GL}(V)) \rtimes W_F$ of the restriction of scalars of $\mathrm{GL}_N$ from $E$ to $F$, with
  $V = \mathbb{C}^N$ and $W_F$ acting through $\mathrm{Gal}(E/F)$ by swapping the two factors. They are the two summands, of
  dimension $N^2$, of the representation of $H$ induced from $\mathrm{Std} \otimes \mathrm{Std} \otimes \mathrm{triv}$ on
  $\mathrm{GL}(V) \times \mathrm{GL}(V) \times W_E$, and an element $w_c$ of $W_F \setminus W_E$ acts on them through the swap of the
  tensor factors with trace $N$ on $\mathrm{Asai}^+$ and $-N$ on $\mathrm{Asai}^-$. Moreover
  $L(s, \varphi, \mathrm{Asai}^-) = L(s, \varphi \otimes \chi^-, \mathrm{Asai}^+)$ for a character $\chi^-$ of the idèle class group
  $\mathbb{A}_E^\times / E^\times$ whose restriction to $\mathbb{A}_F^\times$ is the quadratic character of $E/F$.
- **Non-vanishing** (Shahidi, as Mok states it). Neither $L(s, \varphi, \mathrm{Asai}^+)$ nor $L(s, \varphi, \mathrm{Asai}^-)$
  vanishes at $s = 1$; one of them may have a pole there. Consequently, if $\varphi$ is conjugate self-dual, so that
  $L(s, \varphi \times \varphi^c) = L(s, \varphi \times \varphi^\vee)$ has a simple pole at $s = 1$, exactly one of the two Asai
  $L$-functions has a pole at $s = 1$, and that pole is simple. Which one has the pole is a further theorem, through
  the parity of $\varphi$, not a consequence of the factorization.

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
  (2015), no. 1108, arXiv:1206.0882 (version 5): §2.2, the unnumbered paragraph on pp. 13–14 before Remark 2.2.2 (the
  Asai representations $\mathrm{Asai}^\pm$ as the two summands of an induced representation of $H$, distinguished by the
  trace of $w_c$, after Gan, Gross and Prasad), §2.5, (2.5.9), pp. 35–36 (the factorization of the Rankin–Selberg
  $L$-function, the local factors after Goldberg as special cases of those studied by Shahidi, and, "by Shahidi's theorem
  [S]", the non-vanishing of both Asai $L$-functions at $s = 1$, whence exactly one has a simple pole there), and
  Theorem 2.5.4, p. 36 (which one, through the parity).
- F. Shahidi, "On certain L-functions", Amer. J. Math. 103 (1981), 297–355, cited by Mok as [S]: §5, Theorem 5.1,
  pp. 351–352 (non-vanishing on the line $\operatorname{Re} s = 1$ of products of partial $L$-functions, under hypotheses on
  the local data), of which Mok reports the Asai case; Theorem 5.2 is the application to pairs of general linear groups.
- D. Goldberg, "Some results on reducibility for unitary groups and local Asai L-functions", J. Reine Angew. Math. 448
  (1994), 65–95, as cited by Mok ([G]).
