# Parsimonious exact-one gadget for a three-literal disjunction

There is a fixed set of four exact-one clauses of width three, on three source literals $a, b, c$ and a constant number of auxiliary variables, such that for every assignment of $a,b,c$: if $a \vee b \vee c$ is false there is no one-satisfying extension, and if it is true there is exactly one one-satisfying extension of the auxiliary variables. Likewise there is a positive gadget with a unique one-satisfying assignment that forces a designated variable to $0$, and a positive complement gadget forcing a proxy variable to equal the negation of a given variable with a unique extension.

## Proof sketch

Exhaustive verification of the fixed truth tables of the gadgets of Hunt, Marathe, Radhakrishnan and Stearns.

## Depends on

- [Exact-one satisfiability of a clause formula](exact-one-satisfiability.md)

## Sources

- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998.
