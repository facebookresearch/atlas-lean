# Full-range lemma for dense pointer sets

Let $X \subseteq [m]^n$ be $r$-dense on $F$ and let $Y$ be a set of Bob's inputs with deficiency at most $D$ on the blocks of $F$, both fixed outside $F$. If $16 |F| (D + 1) \le r$, then for every target $\beta \in \{0,1\}^F$ there is $(x, y) \in X \times Y$ with $\mathrm{Ind}_m(x_i, y_i) = \beta_i$ for all $i \in F$. In other words the lifted gadget outputs take every value on the coordinates of $F$ inside the rectangle $X \times Y$.

## Proof sketch

Read each pointer vector as a set of positions; density makes the family of position sets spread, and a sunflower/spread-type argument (or a direct counting of parity tests) shows that a large $Y$ cannot avoid any prescribed pattern on all of these positions.

## Depends on

- [Blockwise-dense sets (blockwise min-entropy)](blockwise-dense-pointer-sets.md)
- [Index gadget and lifted search problems](index-gadget-and-lifted-search-problems.md)

## Sources

- I. Mertz and T. Pitassi, "Lifting: As Easy As 1, 2, 3", ECCC technical report, 2020.
- M. Göös, T. Pitassi and T. Watson, "Query-to-Communication Lifting for BPP", FOCS 2017.
