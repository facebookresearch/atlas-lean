# Lichtenstein's crossover gadget

There is a fixed planar CNF gadget with four boundary variables $a, b, a', b'$ placed in cyclic order $a, b, a', b'$ on its outer face, with clauses of width at most three, such that an assignment of the boundary variables extends to a model of the gadget if and only if $a = a'$ and $b = b'$, and in that case the extension is unique. A version with every internal variable split into implication cycles keeps the property with at most three occurrences per internal variable.

## Proof sketch

Lichtenstein's box introduces copies $a_2\leftrightarrow a$, $b_2\leftrightarrow b$ and four variables with $\alpha\leftrightarrow a_2\wedge b_2$, $\beta\leftrightarrow a_2\wedge b'$, $\gamma\leftrightarrow a'\wedge b'$, $\delta\leftrightarrow a'\wedge b_2$, a clause $\alpha\vee\beta\vee\gamma\vee\delta$ and four binary clauses forbidding cyclically adjacent pairs of $\alpha,\beta,\gamma,\delta$; with the definitions, exactly one of the four is true, and these clauses force $a'\leftrightarrow a$ and $b'\leftrightarrow b$, and all internal variables are functions of $a$ and $b$. Hunt, Marathe, Radhakrishnan and Stearns replace the four-literal clause by $(\alpha\vee\delta\vee\xi)\wedge(\neg\xi\vee\beta\vee\gamma)$ with a fresh $\xi$ that is again determined, giving width three and unique extensions. Splitting each internal variable into copies tied by a cycle of binary implications keeps planarity and uniqueness and leaves at most three occurrences per copy.

## Depends on

- [Planar CNF formulas](planar-cnf-formulas.md)
- [Binary implication cycles and chains](../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/binary-implication-cycles.md)

## Sources

- D. Lichtenstein, "Planar Formulae and Their Uses", SIAM Journal on Computing 11(2), 329–343, 1982.
- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998, Theorem 3.2 and Claim 3.3.
