# Solving Muller games is PSPACE-complete

Deciding whether Eve wins a given finite game with a [Muller objective](muller-rabin-and-streett-objectives.md)
$\mathrm{Muller}(\mathcal{F})$, with $\mathcal{F}$ given as the list of its elements, from a given vertex is PSPACE-complete. Membership
follows from the polynomial-space recursive algorithm; hardness is by a reduction from the evaluation of quantified Boolean
formulas in disjunctive normal form.

## Depends on

- [Muller, Rabin and Streett objectives](muller-rabin-and-streett-objectives.md)

## Proof depends on

- [Büchi–Landweber theorem](buchi-landweber-theorem.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 3 (N. Fijalkow and F. Horn, "Regular games"): Theorem 3.4 and its proof, and the discussion of the representation of $\mathcal{F}$ in Section 3.1.
