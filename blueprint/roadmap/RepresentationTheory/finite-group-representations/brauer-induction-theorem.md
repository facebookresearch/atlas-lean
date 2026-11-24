# Brauer's induction theorem

This node is still to be broken down. It covers Brauer's induction theorem in the virtual form of degree zero that the
inductivity of local constants uses. Let $G$ be a finite group and $F$ a sufficiently large field of characteristic zero,
for instance $\mathbb{C}$. A finite group is $p$-elementary, for a prime $p$, if it is the direct product of a $p$-group and a
cyclic group of order prime to $p$, and elementary if it is $p$-elementary for some $p$; subgroups and quotients of
elementary groups are elementary.

- **Brauer's theorem.** Every virtual representation of $G$ over $F$ is an integral combination of representations induced
  from one-dimensional characters of elementary subgroups.
- **Degree zero** (Deligne). The virtual representations of $G$ of degree zero are spanned over $\mathbb{Z}$ by the
  $\mathrm{Ind}_H^G([\chi] - [1_H])$ for elementary subgroups $H$ and one-dimensional characters $\chi$ of $H$.

## Expansion

A good expansion has statement pages for Brauer's induction theorem and for its degree-zero form, each citing the sources
below with locators. Subtracting $\deg \cdot [1_G]$ from a combination of induced characters does not give the degree-zero
form: it leaves the permutation characters $\mathrm{Ind}_H^G [1_H]$. Česnavičius writes $[1_G] = \sum_i \mathrm{Ind}_{H_i}^G a_i$ with $H_i$
elementary, by Brauer's theorem, and multiplies by a virtual representation $v$ of degree zero; the projection formula
$v \cdot \mathrm{Ind}_H^G a = \mathrm{Ind}_H^G(\mathrm{Res}_H v \cdot a)$ reduces the claim to $G$ elementary. There every irreducible
representation is induced from a one-dimensional character of a subgroup, and one writes
$v = \sum_i n_i \mathrm{Ind}_{H_i}^G [\chi_i]$ through such monomial decompositions of the irreducible constituents of $v$. The centre $Z$ of
$G$ acts by scalars on each irreducible $\mathrm{Ind}_{H_i}^G [\chi_i]$, so it fixes the cosets of $H_i$ that support it and lies in $H_i$.
Then $v = \sum_i n_i \mathrm{Ind}_{H_i}^G([\chi_i] - [1_{H_i}]) + \sum_i n_i \mathrm{Ind}_{H_i}^G [1_{H_i}]$, and the last sum, of degree zero, is inflated
from $G/Z$. The centre $Z$ is nontrivial when $G$ is, an elementary group being the product of a cyclic group and a
$p$-group, so $\# (G/Z) < \# G$ and induction on $\# G$ concludes. For an arbitrary expression of $v$ by induced characters
the inflation fails: for $G$ of order $2$ and $v = \mathrm{Ind}_1^G 1 - 2 \cdot 1_G$, the residual sum is $v$ itself, not inflated from the
trivial quotient.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- K. Česnavičius, "Local factors valued in normal domains", author's version of 15 October 2014,
  <https://webusers.imj-prg.fr/~kestutis.cesnavicius/epsilon-schemes.pdf>: §5.2 (elementary groups) and Proposition 5.3
  and its proof (after Deligne 1973, 1.5: (a) Brauer's theorem over a sufficiently large field, and (b) the virtual
  representations of degree zero are spanned by the $\mathrm{Ind}_H^G([\chi] - [1_H])$, $H$ elementary, through the projection
  formula and induction on the order through the centre).
- J.-P. Serre, *Linear representations of finite groups*, Graduate Texts in Math. 42, Springer, 1977, §12.6, Theorem 27
  (Brauer's induction theorem) and §12.3, proof of Theorem 24 (an elementary group's representations are spanned by
  inductions of one-dimensional characters), as cited by Česnavičius.
- P. Deligne, "Les constantes des équations fonctionnelles des fonctions L", Lecture Notes in Math. 349, Springer, 1973,
  501–596, 1.5, as cited by Česnavičius.
