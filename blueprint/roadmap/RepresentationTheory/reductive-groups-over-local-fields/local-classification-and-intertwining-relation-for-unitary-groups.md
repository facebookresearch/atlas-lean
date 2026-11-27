# Local classification and the local intertwining relation for inner forms of unitary groups

This node is still to be broken down. It covers the two local statements under which Kaletha, Mínguez, Shin and White
prove the endoscopic classification of the discrete spectrum of inner forms of unitary groups. Let $F$ be a local field
of characteristic zero, $E/F$ a quadratic algebra, $G^* = U_{E/F}(N)$ the quasi-split unitary group, $(G, \xi)$ an inner twist
of $G^*$ with a choice $\Xi$ of extended pure inner twist, which determines a character $\chi_\Xi$ of $Z(\hat G^*)^\Gamma$, and $\psi$ a
local Arthur parameter of $G^*$; these are [algebraic groups over a local field](linear-algebraic-groups-over-local-fields.md).
Let $S_\psi = \mathrm{Cent}(\psi, \hat G^*)$ be the centralizer of $\psi$ in the dual group, $S^{\mathrm{rad}}_\psi = (S_\psi \cap \hat G^*_{\mathrm{der}})^\circ$
and $S^\natural_\psi = S_\psi / S^{\mathrm{rad}}_\psi$, a quotient of a complex algebraic group of the dual side that is in general neither
finite nor the component group of $S_\psi$: for the split quadratic algebra $E = F \times F$ and $N = 1$, where $G^* = \mathrm{GL}_1$,
$S_\psi = S^\natural_\psi = \mathbb{C}^\times$ while $\pi_0(S_\psi)$ is trivial. $\mathrm{Irr}(S^\natural_\psi, \chi_\Xi)$ is the set of its irreducible characters whose
pullback to $Z(\hat G^*)^\Gamma$ is $\chi_\Xi$.

- **Local classification** (KMSW, Theorem* 1.6.1, for bounded parameters $\psi$). There are a finite set $\Pi_\psi(G, \Xi)$, an
  index set, with a map to the set of isomorphism classes of irreducible unitary representations of $G(F)$, and a map
  $\pi \mapsto \langle \pi, - \rangle_\Xi$ from $\Pi_\psi(G, \Xi)$ to $\mathrm{Irr}(S^\natural_\psi, \chi_\Xi)$, satisfying the endoscopic character
  identities for matching test functions. The set is empty when $\psi$ is not relevant for $(G, \xi)$. For generic $\psi$ it is
  empty only then, and the map to the unitary dual is injective with tempered image; for other $\psi$ it need not be
  injective.
- **Unbounded localizations** (KMSW, §1.6.4). The packets and pairings extend to the larger set $\Psi^+(G^*)$ of parameters
  whose restriction to the Weil group need not be bounded, by induction from Levi subgroups; the localizations of global
  parameters lie in this set (§1.7), the generalized Ramanujan conjecture not being assumed.
- **Local intertwining relation** (KMSW, Theorem* 2.6.2). For $\psi$ coming from a Levi subgroup $M^*$ and $u$ in the
  group $N_\psi(M^*, G^*)$, with image $u^\natural$ in $N^\natural_\psi(M^*, G^*) = N(A_{\hat M}, S_\psi) / Z(A_{\hat M}, S^{\mathrm{rad}}_\psi)$:
  1. if the packet of $M$ is nonempty and $u^\natural$ lies in $W^{\mathrm{rad}}_\psi(M^*, G^*) = N(A_{\hat M}, S^{\mathrm{rad}}_\psi) / Z(A_{\hat M}, S^{\mathrm{rad}}_\psi)$, the normalized
     self-intertwining operator $R_P(u^\natural, \Xi, \pi, \psi, \psi_F)$ is the identity for every $\pi$ in the packet of $M$;
  2. the linear form $f \mapsto f_{G, \Xi}(\psi, u^\natural)$ defined by these operators on the induced representations depends only on the
     image of $u$ in $S^\natural_\psi$;
  3. $f'_{G, \Xi}(\psi, s_\psi u^{-1}) = e(G) f_{G, \Xi}(\psi, u^\natural)$ when $\psi$ is relevant for $\Xi$, the endoscopic linear form on the left
     vanishing otherwise.

In the edition cited below, Kaletha, Mínguez, Shin and White prove both when $\psi$ is generic and $(G, \xi)$ is realized as a
pure inner twist, and defer the remaining cases to sequels; their global classification for inner forms assumes both,
for the localizations of the global parameter, at every place of a number field (their Hypothesis 3.6.3 and the preamble
of Theorem 5.0.5).

## Expansion

A good expansion has definition pages for extended pure inner twists, local Arthur parameters, their centralizers and
the groups $S^\natural_\psi$, and statement pages for the local classification and for the local intertwining relation, each citing the
source below with locators.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](linear-algebraic-groups-over-local-fields.md), for unitary groups and their inner forms as groups of rational points over a local field; the extended pure inner twists, Arthur parameters, dual groups and the groups $S^\natural_\psi$ are the node's own definitions, as the Expansion says

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Sources

- T. Kaletha, A. Mínguez, S. W. Shin and P.-J. White, "Endoscopic classification of representations: inner forms of
  unitary groups", arXiv:1409.3731: §1.2, p. 56, and §1.6.1, p. 80 ($S_\psi$, $S^{\mathrm{rad}}_\psi$, $S^\natural_\psi$ and
  $\mathrm{Irr}(S^\natural_\psi, \chi_z)$), Theorem* 1.6.1, pp. 80–81 (the local classification, a finite set with a map to the unitary
  dual, with injectivity and tempered image for generic parameters in part 5), §1.6.4, p. 86 (packets for parameters in
  $\Psi^+$), §2.1, p. 90 ($N^\natural_\psi$ and $W^{\mathrm{rad}}_\psi$), §1.7, pp. 88–89, with Remark 1.7.2 (localizations of global parameters, no Ramanujan assumption),
  Theorem* 2.6.2, pp. 112–113 (the
  local intertwining relation, in three parts, with (2.6.2)), Hypothesis 3.6.3, p. 164, and Chapter 5, Theorem 5.0.5,
  pp. 205–206 (the two hypotheses at every place, established for generic parameters of pure inner twists).
