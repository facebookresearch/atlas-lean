# Local converse theorem for GLₙ

Let $F$ be a non-archimedean local field, $G_n = \mathrm{GL}_n(F)$ and $\psi$ a nontrivial
additive character of $F$, and let $\gamma(s, \pi \times \tau, \psi)$ be the $\gamma$-factor of a
pair of irreducible [generic](whittaker-models-for-gl-n.md) representations $\pi$ of $G_n$ and
$\tau$ of $G_r$, from
[the L- and ε-factors of pairs](l-and-epsilon-factors-of-pairs.md).

**Theorem (Jacquet–Liu, Chai).** Let $n \ge 2$ and let $\pi_1$, $\pi_2$ be irreducible generic
representations of $G_n$ with the same central character. If
$\gamma(s, \pi_1 \times \tau, \psi) = \gamma(s, \pi_2 \times \tau, \psi)$ as functions of $s$ for
every irreducible generic representation $\tau$ of $G_r$ and every $r$ with
$1 \le r \le \lfloor n/2 \rfloor$, then $\pi_1 \cong \pi_2$.

If the equality holds for $r = 1$ and one choice of $\psi$, then $\pi_1$ and $\pi_2$ have the same
central character. Henniart had proved, for $n \ge 2$, that equality of the $\gamma$-factors
twisted by all irreducible generic representations of $G_{n-1}$ implies $\pi_1 \cong \pi_2$; and
for two supercuspidal representations of $G_n$, equality of the $\varepsilon$-factors
$\varepsilon(s, \pi_i \times \tau, \psi)$ twisted by all supercuspidal representations $\tau$ of the
$G_r$, $1 \le r \le n-1$, implies $\pi_1 \cong \pi_2$. For $n = 1$ a representation is its central
character.

## Depends on

- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](whittaker-models-for-gl-n.md), for generic representations
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](l-and-epsilon-factors-of-pairs.md), for the $\gamma$- and $\varepsilon$-factors of pairs
- [Smooth and admissible representations of p-adic groups](../representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for central characters
- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for supercuspidal representations, in Henniart's form

## Proof depends on

- [Whittaker models and the Gelfand–Kazhdan theorems for GLₙ](whittaker-models-for-gl-n.md), for Whittaker models and the description of generic representations
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](l-and-epsilon-factors-of-pairs.md), for the local functional equations of the Rankin–Selberg integrals
- [Cuspidal representations and Jacquet's embedding theorem](../representations-of-p-adic-reductive-groups/cuspidal-representations-and-jacquet-embedding.md), for the reduction of Jiang, Nien and Stevens to unitarizable supercuspidal representations

## Sources

- H. Jacquet and B. Liu, "On the local converse theorem for p-adic GL_n", Amer. J. Math. 140
  (2018), arXiv:1601.03656 (version 3): §1, Conjecture 1.1 and Theorem 1.3 ($F$ any
  non-archimedean local field; the remark that equality for $r = 1$ gives the same central
  character, citing Jiang–Nien–Stevens, Corollary 2.7, and the reduction to unitarizable
  supercuspidal representations, their Section 2.4).
- J. Chai, "Bessel functions and local converse conjecture of Jacquet", arXiv:1601.05450
  (version 2): §1, Conjectures 1 and 2 and Theorem 1.1 ($F$ a $p$-adic field).
- G. Henniart, "Caractérisation de la correspondance de Langlands locale par les facteurs ε de
  paires", Invent. Math. 113 (1993), 339–350,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0113>: Théorème 1.1 (generic representations of
  $\mathrm{GL}_n$, $\gamma$-factors twisted by the generic representations of $\mathrm{GL}_{n-1}$)
  and its Corollaire (supercuspidal representations, $\varepsilon$-factors twisted by the
  supercuspidal representations of $\mathrm{GL}_r$, $1 \le r \le n-1$).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states a form for cuspidal representations of $\mathrm{GL}_{m+1}$, with $\varepsilon$-factors
  twisted by $\mathrm{GL}_m$, as `GlobalTheory.Published.LocalConverseGL`.
