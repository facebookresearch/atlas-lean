# Mass production of a constant number of copies

For every constant $c\ge 1$ and every $P>0$ there is $L_0$ such that for all $L\ge L_0$ and every Boolean function $F$ on $L$ inputs, $C(F^{\times c})\le(1+1/P)\,2^L/L$. Consequently a circuit that reads a hard-wired table $F$ at $c$ computed addresses costs at most $(1+1/P)2^L/L$ plus the cost of computing the addresses and combining the $c$ table values.

## Proof sketch

A constant copy count satisfies Uhlig's depth condition, so the bound is the special case $d$ constant of Uhlig's theorem.

## Depends on

- [Mass complexity of a Boolean function](mass-complexity-of-a-boolean-function.md)

## Proof depends on

- [Uhlig's mass-production theorem](uhlig-mass-production-theorem.md)

## Sources

- Dietmar Uhlig, "Networks Computing Boolean Functions for Multiple Input Values", Boolean Function Complexity, 1992.
