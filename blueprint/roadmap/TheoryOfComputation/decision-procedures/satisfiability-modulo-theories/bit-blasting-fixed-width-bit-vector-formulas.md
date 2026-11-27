# Bit-blasting fixed-width bit-vector formulas

Fix a width $w \ge 1$. Translate a quantifier-free bit-vector formula with operations $+$, bitwise $\wedge$, $\vee$, $\neg$, equality and unsigned $<$, all interpreted on $\{0,1\}^w$ with arithmetic modulo $2^w$, by representing each term by $w$ propositional variables, addition by a ripple-carry adder circuit, comparison by a comparator circuit, and then converting the circuit to CNF by the Tseitin transformation. The resulting CNF is satisfiable if and only if the bit-vector formula is.

## Proof depends on

- [Equisatisfiability of the Tseitin transformation](../../../Logic/propositional-logic/tseitin-transformation/cnf-sat-tseitin-bot-iff.md)

## Sources

- D. Kroening and O. Strichman, *Decision Procedures: An Algorithmic Point of View*, 2nd ed., Springer, 2016, Chapter 6; the authors' course slides "Bit-vector flattening" and "Flattening bit-vector arithmetic", <https://www.decision-procedures.org/slides/bit-vectors.pdf>
