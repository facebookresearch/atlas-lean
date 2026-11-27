# Blattner's formula

Let $G$ be a connected semisimple Lie group with a faithful finite-dimensional representation,
$K$ a maximal compact subgroup, $H \subseteq K$ a compact Cartan subgroup, and use the roots $\Phi$,
the lattice $\Lambda$, the Weyl group $W$ and the discrete series representations $\pi_\lambda$,
$\lambda \in \Lambda + \rho_0$ nonsingular, of
[Harish-Chandra's classification of the discrete series](harish-chandra-discrete-series-classification.md).
A root is compact if its root space lies in the complexified Lie algebra $\mathfrak{k}$ of $K$ and
noncompact otherwise; $\Phi^c$ and $\Phi^n$ are the sets of compact and noncompact roots. Let
$\Psi = \{\alpha \in \Phi \mid (\alpha, \lambda) > 0\}$, let $\rho_c$ and $\rho_n$ be half the sums of
the roots in $\Phi^c \cap \Psi$ and in $\Phi^n \cap \Psi$, and let $Q(\mu)$ be the number of ways of
writing $\mu$ as a sum of roots in $\Phi^n \cap \Psi$. Highest weights of irreducible $K$-modules are
taken with respect to $\Phi^c \cap \Psi$.

**Theorem (Hecht–Schmid).** If $\mu \in \Lambda$ is dominant with respect to $\Phi^c \cap \Psi$, the
irreducible $K$-module of highest weight $\mu$ occurs in $\pi_\lambda$ with multiplicity

$$\sum_{w \in W} \varepsilon(w)\, Q\bigl(w(\mu + \rho_c) - \lambda - \rho_n\bigr).$$

Earlier, Schmid had shown that each irreducible $K$-module occurs in $\pi_\lambda$ with at most
this multiplicity, and that discrete series representations are characterized, up to
infinitesimal equivalence, by their restrictions to $K$. For a connected semisimple $G$ with
finite centre, the $K$-module of highest weight $\lambda + \rho_n - \rho_c$ occurs in $\pi_\lambda$
exactly once, and every irreducible $K$-module occurring in $\pi_\lambda$ has a highest weight
$\lambda + \rho_n - \rho_c + A$ with $A$ a sum of roots in $\Psi$.

## Depends on

- [Harish-Chandra's classification of the discrete series](harish-chandra-discrete-series-classification.md), for the parametrization $\lambda \mapsto \pi_\lambda$ and the notation $\Phi$, $\Lambda$, $W$

## Proof depends on

- [Harish-Chandra's classification of the discrete series](harish-chandra-discrete-series-classification.md), for the characters $\Theta_\lambda$
- [Holomorphic discrete series](holomorphic-discrete-series.md), for Schmid's analysis of the Hermitian symmetric case, on which the proof depends
- [Characters, principal series and the Langlands classification for real reductive groups](principal-series-of-real-reductive-groups.md), for the formula for the product of a discrete series character with a finite-dimensional character and the characters of the representations $\mathbf{F}_\lambda$ used in the proof

## Sources

- H. Hecht and W. Schmid, "A proof of Blattner's conjecture", Invent. Math. 31 (1975), 129–154,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0031>: §1, (1.1)–(1.2) and Theorem (1.3) (the
  formula, for $G$ with a faithful finite-dimensional representation; "it was shown in [13] that
  each irreducible K-module occurs in $\pi_\lambda$ at most with the predicted multiplicity"; the
  characterization by restriction to $K$, [13]; "The arguments of this paper depend heavily on
  those of [11]", Schmid's Hermitian symmetric paper, with a product formula of characters), where
  [13] is W. Schmid, "Some properties of square-integrable representations of semi-simple Lie
  groups", Ann. of Math., then to appear.
- M. F. Atiyah and W. Schmid, "A geometric construction of the discrete series for semisimple Lie
  groups", Invent. Math. 42 (1977), 1–62, <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0042>:
  §8, (8.3)–(8.4) and Theorem (8.5) (the $K$-type $\lambda + \rho_n - \rho_c$ occurs exactly once,
  "a weaker, but useful version of Blattner's conjecture").
