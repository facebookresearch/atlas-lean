# Cavalar–Kumar–Rossman: monotone circuit lower bounds from robust sunflowers

There is an explicit monotone function $f_n : \{0,1\}^{n} \to \{0,1\}$ in $\mathrm{NP}$ whose monotone circuit complexity is

$$
\exp\Bigl(\Omega\bigl(n^{1/2}/\log n\bigr)\Bigr),
$$

improving earlier bounds of the form $\exp(n^{1/3 - o(1)})$ for explicit functions. The proof is Razborov's method of approximations in which the sunflower lemma is replaced by the robust sunflower lemma from the improved sunflower bounds.

## Proof sketch

In the approximation method, every intermediate function is approximated by a DNF of bounded width with few terms, and the plucking step uses sunflowers to shrink the DNF. Robust sunflowers, whose cores are hit by a random set with high probability, exist under much weaker size assumptions after the Alweiss-Lovett-Wu-Zhang improvements, which reduces the error introduced by each plucking step and allows a larger width parameter, giving the improved exponent for a suitable Harnik-Raz-type function.

## Depends on

- [Robust sunflowers](../../../Combinatorics/extremal-set-theory/spread-families-and-robust-sunflowers/robust-sunflowers-and-satisfying-systems.md)

## Proof depends on

- [Alweiss–Lovett–Wu–Zhang sunflower bound](../../../Combinatorics/extremal-set-theory/intersecting-families/sunflower-lemma/theorem-1-4.md)
- [Razborov: monotone circuits for clique need superpolynomial size](../monotone-circuit-lower-bound-for-clique/razborov-monotone-clique.md)

## Sources

- B. Cavalar, M. Kumar, B. Rossman, "Monotone circuit lower bounds from robust sunflowers", LATIN (2020); Algorithmica 84 (2022).
- R. Alweiss, S. Lovett, K. Wu, J. Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194 (2021) 795-815; STOC (2020).
- A. A. Razborov, "Lower bounds on the monotone complexity of some Boolean functions", Soviet Mathematics Doklady 31 (1985) 354-357.
