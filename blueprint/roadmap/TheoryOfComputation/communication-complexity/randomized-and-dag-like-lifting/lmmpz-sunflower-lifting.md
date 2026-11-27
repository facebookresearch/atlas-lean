# Lovett–Meka–Mertz–Pitassi–Zhang: lifting with sunflowers

Deterministic query-to-communication lifting holds for the index gadget $\mathrm{IND}_m$ with gadget size $m = n^{1 + \varepsilon}$ for any constant $\varepsilon > 0$ (and a related statement holds for gadgets with larger output): for every search problem $S$ on $n$ bits,

$$
D^{cc}\bigl(S \circ \mathrm{IND}_m^n\bigr) = \Omega\bigl(D^{dt}(S) \cdot \log m\bigr).
$$

The proof replaces the blockwise min-entropy density-restoring argument by spread (robust sunflower) lemmas from the Alweiss–Lovett–Wu–Zhang improvement of the Erdős–Rado sunflower bound.

## Proof sketch

Represent the set of Alice's inputs consistent with a protocol rectangle as a set family over pointers; when it is not spread, the spread lemma finds a small set of coordinates whose fixing increases density by a large factor, which is charged to queries of the decision tree. Spread families have uniform-looking projections under the gadget by a sunflower-type argument (an $\varepsilon$-robust sunflower guarantees the needed full-range property), so the simulation can proceed with smaller gadgets.

## Depends on

- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)

## Proof depends on

- [Alweiss–Lovett–Wu–Zhang sunflower bound](../../../Combinatorics/extremal-set-theory/intersecting-families/sunflower-lemma/theorem-1-4.md)

## Sources

- S. Lovett, R. Meka, I. Mertz, T. Pitassi, J. Zhang, "Lifting with sunflowers", ITCS (2022).
- R. Alweiss, S. Lovett, K. Wu, J. Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194 (2021) 795-815; STOC (2020).
