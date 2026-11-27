# Lichtenstein's crossover gadget

There is a fixed planar CNF gadget with four boundary variables $a, b, a', b'$ placed in cyclic order $a, b, a', b'$ on its outer face, with clauses of width at most three, such that an assignment of the boundary variables extends to a model of the gadget if and only if $a = a'$ and $b = b'$, and in that case the extension is unique. A version with every internal variable split into implication cycles keeps the property with at most three occurrences per internal variable.

## Proof sketch

Verification of a fixed truth table: the gadget realizes $a' = a$ and $b' = b$ through XOR-like subgadgets drawn without crossings; uniqueness of extensions is checked exhaustively.

## Depends on

- [Planar CNF formulas](planar-cnf-formulas.md)
- [Binary implication cycles and chains](../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/binary-implication-cycles.md)

## Sources

- D. Lichtenstein, "Planar Formulae and Their Uses", SIAM Journal on Computing 11(2), 329–343, 1982.
